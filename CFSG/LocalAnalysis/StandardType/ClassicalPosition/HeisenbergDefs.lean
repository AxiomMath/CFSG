module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

@[expose] def scalarAut (F V : Type) [Field F] [AddCommGroup V] [Module F V] :
    Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∃ c : F, ∀ v, g v = c • v}
  one_mem' := ⟨1, fun v => by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, fun v => by simp [hc, hd, smul_smul, mul_comm]⟩
  inv_mem' := by
    rintro a ⟨c, hc⟩
    by_cases hV : Subsingleton V
    · exact ⟨1, fun v => Subsingleton.elim _ _⟩
    · haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hv (a.injective (by simp [hc]))
      refine ⟨c⁻¹, fun w => ?_⟩
      show a.symm w = c⁻¹ • w
      apply a.injective
      rw [LinearEquiv.apply_symm_apply, map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem mem_scalarAut_iff {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {g : V ≃ₗ[F] V} : g ∈ scalarAut F V ↔ ∃ c : F, ∀ v, g v = c • v :=
  Iff.rfl

end CFSG.StandardType.ClassicalPosition.HeisRank
