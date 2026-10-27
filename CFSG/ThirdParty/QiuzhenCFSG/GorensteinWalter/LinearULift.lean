module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod

namespace CFSG
end CFSG
open CFSG

universe u v

namespace CFSG.GorensteinWalter

noncomputable section

private def sl2ULiftEquiv (R : Type v) [CommRing R] :
    Matrix.SpecialLinearGroup (Fin 2) (ULift.{u} R) ≃*
      Matrix.SpecialLinearGroup (Fin 2) R := by
  let f : Matrix.SpecialLinearGroup (Fin 2) (ULift.{u} R) →*
      Matrix.SpecialLinearGroup (Fin 2) R :=
    Matrix.SpecialLinearGroup.map ULift.ringEquiv.toRingHom
  let g : Matrix.SpecialLinearGroup (Fin 2) R →*
      Matrix.SpecialLinearGroup (Fin 2) (ULift.{u} R) :=
    Matrix.SpecialLinearGroup.map ULift.ringEquiv.symm.toRingHom
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · ext x i j
    rfl
  · ext x i j
    rfl

/-- `PSL₂` is invariant under a universe lift of its coefficient ring. -/
public def psl2ULiftEquiv (R : Type v) [CommRing R] :
    PSL2 (ULift.{u} R) ≃* PSL2 R := by
  let e : Matrix.SpecialLinearGroup (Fin 2) (ULift.{u} R) ≃*
      Matrix.SpecialLinearGroup (Fin 2) R := sl2ULiftEquiv R
  apply QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa using congrArg e (hy w)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro z
    apply e.injective
    simpa using hx (e z)

private def gl2ULiftEquiv (R : Type v) [CommRing R] :
    Matrix.GeneralLinearGroup (Fin 2) (ULift.{u} R) ≃*
      Matrix.GeneralLinearGroup (Fin 2) R := by
  let f : Matrix.GeneralLinearGroup (Fin 2) (ULift.{u} R) →*
      Matrix.GeneralLinearGroup (Fin 2) R :=
    Matrix.GeneralLinearGroup.map ULift.ringEquiv.toRingHom
  let g : Matrix.GeneralLinearGroup (Fin 2) R →*
      Matrix.GeneralLinearGroup (Fin 2) (ULift.{u} R) :=
    Matrix.GeneralLinearGroup.map ULift.ringEquiv.symm.toRingHom
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · ext x i j
    rfl
  · ext x i j
    rfl

/-- `PGL₂` is invariant under a universe lift of its coefficient ring. -/
public def pgl2ULiftEquiv (R : Type v) [CommRing R] :
    PGL2 (ULift.{u} R) ≃* PGL2 R := by
  let e : Matrix.GeneralLinearGroup (Fin 2) (ULift.{u} R) ≃*
      Matrix.GeneralLinearGroup (Fin 2) R := gl2ULiftEquiv R
  apply QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa using congrArg e (hy w)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro z
    apply e.injective
    simpa using hx (e z)

end

end CFSG.GorensteinWalter
