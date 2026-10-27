module

public import CFSG.RankThree.GF2n.Smith81.S81UModelData

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Module
  CFSG.RankThree.GF2n.Smith81

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] def IsTotIso (W : Submodule F (Fin 6 → F)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0

@[expose] def IsPt (W : Submodule F (Fin 6 → F)) : Prop :=
  IsTotIso σ W ∧ finrank F W = 3

@[expose] def PtStab (W : Submodule F (Fin 6 → F)) : Subgroup (SUid σ 6) where
  carrier := {g | ∀ w ∈ W, g • w = w}
  mul_mem' {a b} ha hb w hw := by rw [mul_smul, hb w hw, ha w hw]
  one_mem' w _ := one_smul _ w
  inv_mem' {a} ha w hw := by
    calc a⁻¹ • w = a⁻¹ • (a • w) := by rw [ha w hw]
      _ = w := inv_smul_smul a w

theorem mem_ptStab {W : Submodule F (Fin 6 → F)} {g : SUid σ 6} :
    g ∈ PtStab σ W ↔ ∀ w ∈ W, g • w = w := Iff.rfl

@[expose] def orth (S : Submodule F (Fin 6 → F)) : Submodule F (Fin 6 → F) where
  carrier := {v | ∀ w ∈ S, herm σ w v = 0}
  add_mem' {a b} ha hb w hw := by rw [herm_add_right, ha w hw, hb w hw, add_zero]
  zero_mem' w _ := herm_zero_right σ w
  smul_mem' c a ha w hw := by rw [herm_smul_right, ha w hw, mul_zero]

theorem mem_orth {S : Submodule F (Fin 6 → F)} {v : Fin 6 → F} :
    v ∈ orth σ S ↔ ∀ w ∈ S, herm σ w v = 0 := Iff.rfl

@[expose] def NonDeg (U : Submodule F (Fin 6 → F)) : Prop :=
  ∀ x ∈ U, (∀ y ∈ U, herm σ y x = 0) → x = 0

@[expose] def W₀ (F : Type) [Field F] : Submodule F (Fin 6 → F) :=
  Submodule.span F (Set.range e3uT0Vec)

inductive GenPts (X : Set (Submodule F (Fin 6 → F))) : Submodule F (Fin 6 → F) → Prop
  | base {W : Submodule F (Fin 6 → F)} : W ∈ X → GenPts X W
  | line {W W' W'' : Submodule F (Fin 6 → F)} : GenPts X W → GenPts X W' → W ≠ W' →
      IsPt σ W → IsPt σ W' → IsPt σ W'' → finrank F ↥(W ⊓ W') = 2 → W ⊓ W' ≤ W'' → GenPts X W''

end CFSG.RankThree.GF2n.Smith81.S81V
