module

public import CFSG.RankThree.Theta.TwoPlaneComparison
public import CFSG.RankThree.LocalRank.PartTwoCollections

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Assembly.RankThreeEven Subgroup

variable {G : Type} [Group G] [Finite G]

namespace TwoPlane

theorem card_eq_nine_or_eq_of_two_le_pRank {A Y : Subgroup G} (hAcard : Nat.card A = 27)
    (hYA : Y ≤ A) (hY : 2 ≤ CFSG.Assembly.pRank 3 Y) : Nat.card Y = 9 ∨ Y = A := by
  obtain ⟨E, hEY, -, hEcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three Y
  have h9 : 3 ^ 2 ∣ Nat.card Y := by
    refine dvd_trans ?_ (card_dvd_of_le hEY)
    rw [hEcard]
    exact Nat.pow_dvd_pow 3 hY
  have hdvd : Nat.card Y ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hAcard]
    exact card_dvd_of_le hYA
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hk] at h9
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h9
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
  · left
    rw [hk]
    norm_num
  · right
    exact eq_of_le_of_card_ge hYA (by rw [hk, hAcard]; norm_num)

end TwoPlane

theorem two_alpha_criterion_normalizer {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAcard : Nat.card A = 27) (hstar : ∀ a ∈ A, a ≠ 1 → TwoStarConditionAt A a)
    {B : Subgroup G} (hBA : B ≤ A) (hB : Nat.card B = 9) :
    IsPGroup 2 (twoAlpha B) ∧
      (∀ D : Subgroup G, D ≤ A → Nat.card D = 9 → twoAlpha D = twoAlpha B) ∧
      aschCore 2 3 A ≤ normalizer (twoAlpha B : Set G) := by
  have hmix := twoMixedBalance_of_twoStar hA hAcard hstar
  have hB0 : B ≠ ⊥ := fun h => by
    rw [h, card_bot] at hB
    norm_num at hB
  have hind : ∀ D : Subgroup G, D ≤ A → Nat.card D = 9 → twoAlpha D = twoAlpha B :=
    fun D hDA hD => twoAlpha_hyperplane_independence hA hAcard hstar hDA hD hBA hB
  refine ⟨isPGroup_twoAlpha hA hAcard hmix hBA hB0, hind, ?_⟩
  refine sSup_le ?_
  rintro _ ⟨Y, hYA, hY2, -, rfl⟩
  rcases TwoPlane.card_eq_nine_or_eq_of_two_le_pRank hAcard hYA hY2 with hY | rfl
  · rw [← hind Y hYA hY]
    exact normalizer_le_normalizer_twoAlpha Y
  · intro g hg
    refine SteinbergBY.mem_normalizer_of_map_conj_eq ?_
    have hBg : B.map (MulAut.conj g).toMonoidHom ≤ Y := by
      rw [← SteinbergBY.map_conj_eq_of_mem_normalizer hg]
      exact map_mono hBA
    have hBgcard : Nat.card (B.map (MulAut.conj g).toMonoidHom) = 9 := by
      rw [card_map_of_injective (MulAut.conj g).injective, hB]
    rw [twoAlpha_map_equiv, hind _ hBg hBgcard]

theorem two_alpha_criterion {A : Subgroup G} (hA : A ∈ partTwoE G)
    (hstar : ∀ a ∈ A, a ≠ 1 → TwoStarConditionAt A a) {B : Subgroup G} (hBA : B ≤ A)
    (hB : Nat.card B = 9) (hne : twoAlpha B ≠ ⊥) : A ∈ partTwoT G := by
  obtain ⟨h2, -, hN⟩ := two_alpha_criterion_normalizer hA.1 hA.2.1 hstar hBA hB
  exact ⟨hA, normalizer (twoAlpha B : Set G), ⟨twoAlpha B, hne, h2, rfl⟩, hN⟩

end CFSG.RankThree.Theta
