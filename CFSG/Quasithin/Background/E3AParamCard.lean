module

public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.Quasithin.E3

variable {W : Type} [CommGroup W] [Finite W]

theorem aParam_le_of_card_le (X : Subgroup (MulAut W)) {n : ℕ}
    (h : ∀ A : Subgroup (MulAut W), A ≤ X → (∀ a ∈ A, a ^ 2 = 1) → Nat.card A ≤ 2 ^ n) :
    aParam X ≤ n := by
  classical
  refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty X n ?_
  intro A hA
  simp only [aSet, Set.mem_setOf_eq] at hA
  obtain ⟨hAX, hAne, hAel, hAfix⟩ := hA
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hAel.2
  have hAcard : Nat.card A ≤ 2 ^ n := h A hAX hA2
  have hAp : IsPGroup 2 (↥A) := fun a =>
    ⟨1, Subtype.ext (by simpa using hA2 (a : MulAut W) a.2)⟩
  have hm : mQuot A ⊥ ≤ n := by
    have h1 : Nat.card A = 2 ^ mQuot A ⊥ := by
      rw [← relIndex_eq_two_pow hAp ⊥, Subgroup.relIndex_bot_left]
    rw [h1] at hAcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hAcard
  have hfix : fixV (⊥ : Subgroup (MulAut W)) = fixV A :=
    hAfix ⊥ bot_le (by omega)
  have htop : fixV A = ⊤ := by
    rw [← hfix]
    ext v
    simp [fixV]
  have hAeq : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV A := by rw [htop]; exact Subgroup.mem_top v
    exact mem_fixV.mp hv a ha
  exact hAne hAeq

end CFSG.Quasithin.E3
