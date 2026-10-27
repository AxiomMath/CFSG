module

public import CFSG.LocalAnalysis.StandardType.GGTBJR1OmPlusRow
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggOmPlusPlusRowEven_recipe_adjoint
    {m n p : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m) (hmo : Odd m) (hpn : p ∣ 2 ^ n + 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaPlus (m + 1) (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus (m + 1) (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ (r m' n' : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
        (_ : R ≃* OrthRest.RPlus K (m' + 1)),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n' ∧ 1 ≤ n' ∧ 3 ≤ m' ∧ Odd m' ∧ p ∣ 2 ^ n' + 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 0, m, n, K, inferInstance, inferInstance,
    MulEquiv.refl _, TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus (by omega : 4 ≤ m + 1)),
    hK, hn, hm, hmo, hpn, fun φ hφ => hφ⟩

private theorem ggOmPlusPlusRowOdd_recipe_adjoint
    {m n p : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m) (hme : Even m) (hpn : p ∣ 2 ^ n + 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaPlus (m + 1) (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus (m + 1) (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ (r m' n' : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
        (_ : R ≃* OrthRest.RPlus K (m' + 1)),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n' ∧ 1 ≤ n' ∧ 3 ≤ m' ∧ Even m' ∧ p ∣ 2 ^ n' + 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 0, m, n, K, inferInstance, inferInstance,
    MulEquiv.refl _, TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus (by omega : 4 ≤ m + 1)),
    hK, hn, hm, hme, hpn, fun φ hφ => hφ⟩

theorem ggOmPlusPlusRowEven_labelAll_adjoint
    {p : ℕ} {lab : LargeEvenLabel} (hq : 1 ≤ lab.n)
    (h : lab.tag = .D ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (r m n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : R ≃* OrthRest.RPlus K (m + 1)),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n ∧ 1 ≤ n ∧ 3 ≤ m ∧ Odd m ∧ p ∣ 2 ^ n + 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, h4, heven, hpn⟩ := h
  subst htag
  dsimp only at h4 heven hpn hq
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2
  · omega
  · rw [← Nat.sub_add_cancel (by omega : 1 ≤ l)] at hQ ⊢
    exact ggOmPlusPlusRowEven_recipe_adjoint hq (by omega : 3 ≤ l - 1)
      (by obtain ⟨j, hj⟩ := heven; exact ⟨j - 1, by omega⟩) hpn hQ

theorem ggOmPlusPlusRowOdd_labelAll_adjoint
    {p : ℕ} {lab : LargeEvenLabel} (hq : 1 ≤ lab.n)
    (h : lab.tag = .D ∧ 4 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (r m n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : R ≃* OrthRest.RPlus K (m + 1)),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n ∧ 1 ≤ n ∧ 3 ≤ m ∧ Even m ∧ p ∣ 2 ^ n + 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, h4, hodd, hpn⟩ := h
  subst htag
  dsimp only at h4 hodd hpn hq
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2
  · omega
  · rw [← Nat.sub_add_cancel (by omega : 1 ≤ l)] at hQ ⊢
    exact ggOmPlusPlusRowOdd_recipe_adjoint hq (by omega : 3 ≤ l - 1)
      (by obtain ⟨j, hj⟩ := hodd; exact ⟨j, by omega⟩) hpn hQ

end CFSG.StandardType

end
