module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConcl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W]

theorem s16c1610_not_concl614_of_normal_big [Finite W] {G X N : Subgroup (MulAut W)} {m₀ : ℕ}
    (hm₀ : 4 ≤ m₀) (hr : 2 * m₀ ≤ rk W + 1) (hNG : N ≤ G)
    (hNX : N ≤ Subgroup.centralizer (X : Set (MulAut W)))
    (hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h9 : 9 < Nat.card N)
    (hN : Nat.card N < 2 ^ (m₀ * m₀ - 2)) : ¬ Concl614 W G X := by
  have hNpos : 0 < Nat.card N := by omega
  have hnd : ∀ c : ℕ, 0 < c → c < Nat.card N → ¬ Nat.card N ∣ c := fun c hc0 hc hd =>
    absurd (Nat.le_of_dvd hc0 hd) (by omega)
  have hpow : ∀ m : ℕ, m₀ ≤ m → 2 ^ (m₀ * m₀ - 2) ≤ 2 ^ (m * m - 2) := fun m hm =>
    Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right (Nat.mul_le_mul hm hm) 2)
  rintro ((⟨m', h⟩ | ⟨m', h⟩ | ⟨-, hW⟩) | ⟨m', h⟩)
  · have h1 := s16c1610_rk_eq_of_card (s16c1610_card_of_isTensorS3L2 h).2
    have hm : m₀ ≤ m' := by omega
    exact s16c1610_not_isTensorS3L2_of_normal (by omega) hNG hNn (hnd 6 (by norm_num) (by omega))
      (s16c1610_not_dvd_card_GL_two hNpos (hN.trans_le (hpow m' hm))) h
  · have h1 := s16c1610_rk_eq_of_card (s16c1610_card_of_isNatGL4 h).2
    have hm : m₀ ≤ m' := by omega
    have hKm : Nat.card N < 2 ^ (2 * m' * m' - 3) :=
      hN.trans_le ((hpow m' hm).trans (Nat.pow_le_pow_right (by norm_num) (by
        have h0 : 0 < m' * m' := Nat.mul_pos (by omega) (by omega)
        have h2 : 2 * m' * m' = 2 * (m' * m') := Nat.mul_assoc 2 m' m'
        omega)))
    exact s16c1610_not_isNatGL4_of_normal (by omega) (le_inf hNG hNX) hNn (hnd 9 (by norm_num) h9)
      (s16c1610_not_dvd_card_SL_four (by omega) hNpos hKm) h
  · have h6 : rk W = 2 * 3 := s16c1610_rk_eq_of_card (m := 3) (by rw [hW]; norm_num)
    omega
  · have h1 := s16c1610_rk_eq_of_card (s16c1610_card_of_isNatSL4 h).2
    have hm : m₀ ≤ m' := by omega
    have hKm : Nat.card N < 2 ^ (2 * m' * m' - 3) :=
      hN.trans_le ((hpow m' hm).trans (Nat.pow_le_pow_right (by norm_num) (by
        have h0 : 0 < m' * m' := Nat.mul_pos (by omega) (by omega)
        have h2 : 2 * m' * m' = 2 * (m' * m') := Nat.mul_assoc 2 m' m'
        omega)))
    exact s16c1610_not_isNatSL4_of_normal (by omega) (le_inf hNG hNX) hNn (hnd 9 (by norm_num) h9)
      (s16c1610_not_dvd_card_SL_four (by omega) hNpos hKm) h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
