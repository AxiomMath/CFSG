module

public import CFSG.Quasithin.Background.A3Structure320
public import CFSG.Quasithin.Vol2.Ch11SecE3LieLow
public import CFSG.Quasithin.Vol2.Ch11SecOE8D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

open Matrix CFSG.CGT.Timmesfeld75 CFSG.LinearGroups CFSG.Quasithin
open scoped MatrixGroups Pointwise LinearAlgebra.Projectivization

section Transport

variable {X : Type*} [Group X] [Finite X]

theorem solvRad_map_equiv (β : X ≃* X) (R : Subgroup X) :
    solvRad (R.map β.toMonoidHom) = (solvRad R).map β.toMonoidHom := by
  refine le_antisymm ?_ (A320.map_solvRad_le β.toMonoidHom R)
  have h := A320.map_solvRad_le β.symm.toMonoidHom (R.map β.toMonoidHom)
  have hR : (R.map β.toMonoidHom).map β.symm.toMonoidHom = R := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id R
    ext x
    simp
  rw [hR] at h
  intro x hx
  refine ⟨β.symm x, h ⟨x, hx, rfl⟩, by simp⟩

theorem relIndex_solvRad_map (β : X ≃* X) (V R : Subgroup X) :
    (V.map β.toMonoidHom ⊓ solvRad (R.map β.toMonoidHom)).relIndex (V.map β.toMonoidHom) =
      (V ⊓ solvRad R).relIndex V := by
  rw [solvRad_map_equiv, ← Subgroup.map_inf _ _ _ β.injective,
    Subgroup.relIndex_map_map_of_injective _ _ β.injective]

omit [Finite X] in
theorem isSolvable_map_equiv_iff (β : X ≃* X) (R : Subgroup X) :
    Group.IsSolvable ↥(R.map β.toMonoidHom) ↔ Group.IsSolvable ↥R := by
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (R.equivMapOfInjective β.toMonoidHom β.injective).toMonoidHom)
      (MulEquiv.injective _)
  · intro h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (R.equivMapOfInjective β.toMonoidHom β.injective).symm.toMonoidHom)
      (MulEquiv.injective _)

end Transport

variable {F : Type} [Field F] [Finite F] [CharP F 2]

noncomputable abbrev ppt (F : Type) [Field F] (i : Fin 3) : ℙ F (Fin 3 → F) :=
  Projectivization.mk'' (pt F i) (finrank_pt i)

omit [Finite F] [CharP F 2] in
theorem conjSub_projectiveElation (g : SL(3, F)) (L : Submodule F (Fin 3 → F)) :
    A1b.conjSub (piP F g) (projectiveElationSubgroup L) = projectiveElationSubgroup (g • L) := by
  rw [projectiveElationSubgroup, projectiveElationSubgroup, ← SecE3.map_conjSub,
    ← conj_smul_elationSubgroup]
  rfl

omit [Finite F] [CharP F 2] in
theorem smul_eq_of_smul_ppt {g : SL(3, F)} {i j : Fin 3} (h : piP F g • ppt F i = ppt F j) :
    g • pt F i = pt F j := by
  have h1 := congrArg Projectivization.submodule h
  rw [show piP F g • ppt F i = g • ppt F i from rfl, PSL.smul_submodule,
    Projectivization.submodule_mk'', Projectivization.submodule_mk''] at h1
  exact h1

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3
