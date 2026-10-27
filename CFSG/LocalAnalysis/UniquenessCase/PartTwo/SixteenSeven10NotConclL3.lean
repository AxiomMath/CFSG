module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConcl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W]

theorem s16c1610_not_concl614_of_normal_l3 [Finite W] {G X N : Subgroup (MulAut W)}
    (hXG : X ≤ G) (hX : Nat.card X = 3) (hr : 6 ≤ rk W) (hNG : N ≤ G)
    (hNX : N ≤ Subgroup.centralizer (X : Set (MulAut W)))
    (hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hN : Nat.card N = 168 * 168) :
    ¬ Concl614 W G X := by
  have hNpos : 0 < Nat.card N := by rw [hN]; norm_num
  have hnd : ∀ c : ℕ, 0 < c → c < Nat.card N → ¬ Nat.card N ∣ c := fun c hc0 hc hd =>
    absurd (Nat.le_of_dvd hc0 hd) (by omega)
  rintro ((⟨m, h⟩ | ⟨m, h⟩ | ⟨hS6, -⟩) | ⟨m, h⟩)
  · obtain ⟨hG, hW⟩ := s16c1610_card_of_isTensorS3L2 h
    have h1 := s16c1610_rk_eq_of_card hW
    have hm : 3 ≤ m := by omega
    by_cases hm5 : 5 ≤ m
    · refine s16c1610_not_isTensorS3L2_of_normal hm hNG hNn (hnd 6 (by norm_num) (by omega))
        (s16c1610_not_dvd_card_GL_two hNpos ?_) h
      calc Nat.card N < 2 ^ 23 := by rw [hN]; norm_num
        _ ≤ 2 ^ (m * m - 2) := Nat.pow_le_pow_right (by norm_num)
            (by have := Nat.mul_le_mul hm5 hm5; omega)
    · have hdvd : Nat.card N ∣ Nat.card G := Subgroup.card_dvd_of_le hNG
      rw [hG, hN, s16c1610_card_GL_two] at hdvd
      have hm34 : m = 3 ∨ m = 4 := by omega
      rcases hm34 with rfl | rfl
      · simp [Fin.prod_univ_succ] at hdvd
      · simp [Fin.prod_univ_succ] at hdvd
  · obtain ⟨-, hW⟩ := s16c1610_card_of_isNatGL4 h
    have h1 := s16c1610_rk_eq_of_card hW
    have hm : 3 ≤ m := by omega
    refine s16c1610_not_isNatGL4_of_normal (by omega) (le_inf hNG hNX) hNn
      (hnd 9 (by norm_num) (by omega)) (s16c1610_not_dvd_card_SL_four (by omega) hNpos ?_) h
    calc Nat.card N < 2 ^ 15 := by rw [hN]; norm_num
      _ ≤ 2 ^ (2 * m * m - 3) := Nat.pow_le_pow_right (by norm_num)
          (by have := Nat.mul_le_mul hm hm; have h2 : 2 * m * m = 2 * (m * m) := Nat.mul_assoc 2 m m
              omega)
  · have hG := s16c1610_card_of_isS6Cover hXG hS6
    have hle : Nat.card N ≤ Nat.card G := Subgroup.card_le_of_le hNG
    rw [hG, hX, hN] at hle
    omega
  · obtain ⟨-, hW⟩ := s16c1610_card_of_isNatSL4 h
    have h1 := s16c1610_rk_eq_of_card hW
    have hm : 3 ≤ m := by omega
    refine s16c1610_not_isNatSL4_of_normal (by omega) (le_inf hNG hNX) hNn
      (hnd 9 (by norm_num) (by omega)) (s16c1610_not_dvd_card_SL_four (by omega) hNpos ?_) h
    calc Nat.card N < 2 ^ 15 := by rw [hN]; norm_num
      _ ≤ 2 ^ (2 * m * m - 3) := Nat.pow_le_pow_right (by norm_num)
          (by have := Nat.mul_le_mul hm hm; have h2 : 2 * m * m = 2 * (m * m) := Nat.mul_assoc 2 m m
              omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
