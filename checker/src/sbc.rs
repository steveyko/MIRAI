use crate::block_visitor::BlockVisitor;
use crate::path::{PathEnum, PathRefinement, PathSelector};
use rustc_middle::mir;
use rustc_middle::ty::TyKind;
use std::fmt::{Debug, Formatter, Result};

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Status {
    NoRef,
    Aliased,
    Mutable,
    Mutated,
}

impl Debug for Status {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Status::NoRef => f.write_str("NoRef"),
            Status::Aliased => f.write_str("Aliased"),
            Status::Mutable => f.write_str("Mutable"),
            Status::Mutated => f.write_str("Mutated"),
        }
    }
}

pub fn check_assign<'block, 'analysis, 'compilation, 'tcx>(
    block_visitor: &mut BlockVisitor<'block, 'analysis, 'compilation, 'tcx>,
    place: &mir::Place<'tcx>,
    rvalue: &mir::Rvalue<'tcx>,
) {
    let path = block_visitor.visit_lh_place(place);

    // This checks the L value to see if it's used properly according to the borrow rules and
    // updates the status to Mutated.
    match &path.value {
        PathEnum::QualifiedPath { selector, .. } if *selector.as_ref() == PathSelector::Deref => {
            let path = path.canonicalize(&block_visitor.bv.current_environment);
            match block_visitor.bv.current_environment.status_at(&path) {
                Some(vec) if vec.iter().find(|&x| *x == Status::Mutable) == None => {
                    error!("{:?} not mutable", path);
                }
                Some(vec) if vec.len() > 1 => {
                    error!("{:?} not exclusive but being assigned", path);
                }
                _ => {}
            }
            block_visitor
                .bv
                .current_environment
                .update_status_at(path.clone(), Status::Mutated);
        }
        _ => {}
    }

    // This checks the R value to see how it's used.
    match rvalue {
        // This is when a (read-only) alias is used after the referent is mutated.
        mir::Rvalue::Use(mir::Operand::Copy(rplace))
        | mir::Rvalue::Use(mir::Operand::Move(rplace)) => {
            let rpath = block_visitor
                .visit_rh_place(rplace)
                .canonicalize(&block_visitor.bv.current_environment);
            if let PathEnum::LocalVariable { .. } = &rpath.value {
                if let Some(vec) = block_visitor.bv.current_environment.status_at(&rpath) {
                    if vec.iter().find(|&x| *x == Status::Mutated) != None {
                        error!("{:?} mutated then accessed", rpath);
                    }
                }
            }
        }
        // This is when a reference is declared. We need to update its status.
        mir::Rvalue::Ref(_, _, place) | mir::Rvalue::AddressOf(_, place) => {
            let target_type = block_visitor
                .type_visitor()
                .get_path_rustc_type(&path, block_visitor.bv.current_span);
            let value_path = block_visitor.visit_lh_place(place);
            match &value_path.value {
                PathEnum::LocalVariable { .. } => match target_type.kind() {
                    TyKind::Ref(_, _, rustc_hir::Mutability::Mut) => {
                        block_visitor
                            .bv
                            .current_environment
                            .update_status_at(value_path.clone(), Status::Mutable);
                    }
                    TyKind::Ref(_, _, rustc_hir::Mutability::Not) => {
                        block_visitor
                            .bv
                            .current_environment
                            .update_status_at(value_path.clone(), Status::Aliased);
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        _ => {}
    }
}
