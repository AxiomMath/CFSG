module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10CardLem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NormalTensor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NormalGL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NormalS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W]

theorem s16c1610_not_dvd_card_GL_two {m K : ℕ} (hK : 0 < K) (hKm : K < 2 ^ (m * m - 2)) :
    ¬ Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) ∣ K := fun h =>
  absurd (lt_of_lt_of_le hKm ((s16c1610_two_pow_le_card_GL_two m).trans (Nat.le_of_dvd hK h)))
    (lt_irrefl _)

theorem s16c1610_not_dvd_card_SL_four {m K : ℕ} (hm : 2 ≤ m) (hK : 0 < K)
    (hKm : K < 2 ^ (2 * m * m - 3)) :
    ¬ Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) ∣ K := fun h =>
  absurd (lt_of_lt_of_le hKm ((s16c1610_two_pow_le_card_SL_four m hm).trans (Nat.le_of_dvd hK h)))
    (lt_irrefl _)

theorem s16c1610_not_concl614_of_normal [Finite W] {G X N : Subgroup (MulAut W)} {m : ℕ}
    (hm : rk W = 2 * m) (hm3 : 3 ≤ m) (hNG : N ≤ G)
    (hNX : N ≤ Subgroup.centralizer (X : Set (MulAut W)))
    (hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h6 : ¬ Nat.card N ∣ 6)
    (hGL : ¬ Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) ∣ Nat.card N)
    (h9 : ¬ Nat.card N ∣ 9)
    (hSL : ¬ Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) ∣ Nat.card N)
    (h6c : m = 3 → X ≤ N ∧ (Nat.card N = 3 * Nat.card X ∨ Nat.card N = 9 * Nat.card X)) :
    ¬ Concl614 W G X := by
  rintro ((⟨m', h⟩ | ⟨m', h⟩ | ⟨hS6, hW⟩) | ⟨m', h⟩)
  · have h1 := s16c1610_rk_eq_of_card (s16c1610_card_of_isTensorS3L2 h).2
    have hmm : m' = m := by omega
    subst hmm
    exact s16c1610_not_isTensorS3L2_of_normal hm3 hNG hNn h6 hGL h
  · have h1 := s16c1610_rk_eq_of_card (s16c1610_card_of_isNatGL4 h).2
    have hmm : m' = m := by omega
    subst hmm
    exact s16c1610_not_isNatGL4_of_normal (by omega) (le_inf hNG hNX) hNn h9 hSL h
  · have h1 : rk W = 2 * 3 := s16c1610_rk_eq_of_card (m := 3) (by rw [hW]; norm_num)
    obtain ⟨hXN, hord⟩ := h6c (by omega)
    exact s16c1610_not_isS6Cover_of_normal hXN hNG hNn hord hS6
  · have h1 := s16c1610_rk_eq_of_card (s16c1610_card_of_isNatSL4 h).2
    have hmm : m' = m := by omega
    subst hmm
    exact s16c1610_not_isNatSL4_of_normal (by omega) (le_inf hNG hNX) hNn h9 hSL h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
