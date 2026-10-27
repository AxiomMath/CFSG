module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Quad

public section

namespace CFSG.Quasithin.H13.F431.F45

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin

namespace PgGeom

abbrev V3 (F : Type) := Fin 3 → F

section Action

variable {F : Type} [Field F]

@[expose] def slMap (M : SpecialLinearGroup (Fin 3) F) (U : Submodule F (V3 F)) :
    Submodule F (V3 F) :=
  U.map (mulVecLin (M : Matrix (Fin 3) (Fin 3) F))

theorem slMap_one (U : Submodule F (V3 F)) : slMap 1 U = U := by
  show U.map (mulVecLin (1 : Matrix (Fin 3) (Fin 3) F)) = U
  rw [mulVecLin_one, Submodule.map_id]

theorem slMap_mul (M N : SpecialLinearGroup (Fin 3) F) (U : Submodule F (V3 F)) :
    slMap (M * N) U = slMap M (slMap N U) := by
  show U.map (mulVecLin ((M : Matrix (Fin 3) (Fin 3) F) * (N : Matrix (Fin 3) (Fin 3) F))) =
    (U.map (mulVecLin (N : Matrix (Fin 3) (Fin 3) F))).map
      (mulVecLin (M : Matrix (Fin 3) (Fin 3) F))
  rw [mulVecLin_mul, Submodule.map_comp]

theorem mulVecLin_injective (M : SpecialLinearGroup (Fin 3) F) :
    Function.Injective (mulVecLin (M : Matrix (Fin 3) (Fin 3) F)) := by
  have h2 : ∀ v : V3 F, mulVecLin ((M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      (mulVecLin (M : Matrix (Fin 3) (Fin 3) F) v) = v := fun v => by
    rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, coe_inv_mul_coe, one_mulVec]
  exact Function.LeftInverse.injective h2

theorem finrank_slMap (M : SpecialLinearGroup (Fin 3) F) (U : Submodule F (V3 F)) :
    Module.finrank F (slMap M U) = Module.finrank F U :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (mulVecLin_injective M) U)).symm

theorem slMap_le_iff (M : SpecialLinearGroup (Fin 3) F) {U U' : Submodule F (V3 F)} :
    slMap M U ≤ slMap M U' ↔ U ≤ U' :=
  Submodule.map_le_map_iff_of_injective (mulVecLin_injective M) U U'

theorem slMap_scalar {s : SpecialLinearGroup (Fin 3) F} (hs : s ∈ scalars 3 F)
    (U : Submodule F (V3 F)) : slMap s U = U :=
  mem_stabilizer.mp (scalars_le_stabilizer U hs)

@[expose] def slPerm : SpecialLinearGroup (Fin 3) F →* Equiv.Perm (Submodule F (V3 F)) where
  toFun M :=
    { toFun := slMap M
      invFun := slMap M⁻¹
      left_inv := fun U => by rw [← slMap_mul, inv_mul_cancel, slMap_one]
      right_inv := fun U => by rw [← slMap_mul, mul_inv_cancel, slMap_one] }
  map_one' := Equiv.ext slMap_one
  map_mul' M N := Equiv.ext fun U => slMap_mul M N U

@[expose] def xPerm : projectiveSL 3 F →* Equiv.Perm (Submodule F (V3 F)) :=
  QuotientGroup.lift (scalars 3 F) slPerm
    (fun _ hM => Equiv.ext fun U => slMap_scalar hM U)

theorem xPerm_proj (M : SpecialLinearGroup (Fin 3) F) (U : Submodule F (V3 F)) :
    xPerm (proj 3 F M) U = slMap M U := rfl

theorem finrank_xPerm (x : projectiveSL 3 F) (U : Submodule F (V3 F)) :
    Module.finrank F (xPerm x U) = Module.finrank F U := by
  obtain ⟨M, rfl⟩ := proj_surjective 3 F x
  rw [xPerm_proj, finrank_slMap]

@[expose] def Sub3 (F : Type) [Field F] (n : ℕ) : Type :=
  {U : Submodule F (V3 F) // Module.finrank F U = n}

instance (n : ℕ) : MulAction (projectiveSL 3 F) (Sub3 F n) where
  smul x p := ⟨xPerm x p.1, by rw [finrank_xPerm]; exact p.2⟩
  one_smul p := Subtype.ext (by
    show xPerm 1 p.1 = p.1
    rw [map_one]
    rfl)
  mul_smul x y p := Subtype.ext (by
    show xPerm (x * y) p.1 = xPerm x (xPerm y p.1)
    rw [map_mul]
    rfl)

instance [Finite F] (n : ℕ) : Finite (Sub3 F n) :=
  inferInstanceAs (Finite {_U : Submodule F (V3 F) // _})

abbrev Pt (F : Type) [Field F] : Type := Sub3 F 1

abbrev Ln (F : Type) [Field F] : Type := Sub3 F 2

@[expose] def inc (p : Pt F) (L : Ln F) : Prop := p.1 ≤ L.1

theorem inc_smul (x : projectiveSL 3 F) (p : Pt F) (L : Ln F) : inc (x • p) (x • L) ↔ inc p L := by
  obtain ⟨M, rfl⟩ := proj_surjective 3 F x
  exact slMap_le_iff M

abbrev Gr (F : Type) [Field F] : SimpleGraph (Pt F ⊕ Ln F) := incGraph inc

instance : GraphAction (projectiveSL 3 F) (Gr F) where
  adj_smul g a b := by
    cases a <;> cases b
    · exact Iff.rfl
    · exact inc_smul g _ _
    · exact inc_smul g _ _
    · exact Iff.rfl

end Action

end PgGeom

end CFSG.Quasithin.H13.F431.F45
