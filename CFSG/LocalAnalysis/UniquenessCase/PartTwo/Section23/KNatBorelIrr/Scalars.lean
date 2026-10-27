module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Ring.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

variable {W : Type} [CommGroup W] {ι : Type} {K : Type} [Field K]

private lemma eq_one_of_toAdd_eq_zero_L01 (e : W ≃* Multiplicative (ι → K))
    {y : W} (h : Multiplicative.toAdd (e y) = 0) : y = 1 := by
  have he : e y = 1 := by simpa using h
  exact e.injective (by rw [map_one]; exact he)

theorem eq_bot_or_eq_of_scalar_stable (e : W ≃* Multiplicative (ι → K)) (v₀ : ι → K)
    (F J : Subgroup W)
    (hF : ∀ y : W, y ∈ F ↔ ∃ c : K, Multiplicative.toAdd (e y) = c • v₀) (hJF : J ≤ F)
    (hJ : ∀ c : K, c ≠ 0 → ∀ y ∈ J,
      ∃ y' ∈ J, Multiplicative.toAdd (e y') = c • Multiplicative.toAdd (e y)) :
    J = ⊥ ∨ J = F := by
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  · refine Or.inr (le_antisymm hJF ?_)
    obtain ⟨⟨y, hyJ⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hJ0
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨a, ha⟩ := (hF y).1 (hJF hyJ)
    have ha0 : a ≠ 0 := by
      intro ha'
      have hy0 : Multiplicative.toAdd (e y) = 0 := by
        rw [ha, ha', zero_smul]
      exact hy1' (eq_one_of_toAdd_eq_zero_L01 e (y := y) hy0)
    intro z hz
    obtain ⟨b, hb⟩ := (hF z).1 hz
    by_cases hb0 : b = 0
    · have hz0 : Multiplicative.toAdd (e z) = 0 := by
        rw [hb, hb0, zero_smul]
      rw [eq_one_of_toAdd_eq_zero_L01 e (y := z) hz0]
      exact one_mem J
    · obtain ⟨y', hy'J, hy'⟩ := hJ (b * a⁻¹) (mul_ne_zero hb0 (inv_ne_zero ha0)) y hyJ
      have hby : Multiplicative.toAdd (e y') = Multiplicative.toAdd (e z) := by
        rw [hy', ha, hb, smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
      have hyz : y' = z := e.injective (Multiplicative.toAdd.injective hby)
      rwa [hyz] at hy'J

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
