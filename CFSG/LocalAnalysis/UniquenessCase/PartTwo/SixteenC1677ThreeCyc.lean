module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section ThreeFour

variable {W : Type} [CommGroup W]

theorem s168e3_pRank_lt_two_of_z3_four [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 4) {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsElemAbelianOfRank 3 1 ↥L)
    (hWL : commSub ⊤ L = ⊤) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    CFSG.Open.pRank q A < 2 :=
  s168e3_pRank_lt_two_of_rk_le_four hW (d := 4) le_rfl hcard hq
    (hq.five_le_of_ne_two_of_ne_three hq2 hq3) A

end ThreeFour

section SevenSix

variable {W : Type} [CommGroup W]

private theorem s168e3_cyc_card_GL_six :
    Nat.card (GL (Fin 6) (ZMod 2)) = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

private theorem s168e3_cyc_not_sq_dvd_GL_six {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hq7 : q ≠ 7) : ¬ q ^ 2 ∣ 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by
  intro h
  have hqN : q ∣ 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 :=
    dvd_trans (dvd_pow_self q (n := 2) (by norm_num)) h
  have hmem : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 31 := by
    rcases (hq.dvd_mul).1 hqN with h' | h'
    · rcases (hq.dvd_mul).1 h' with h' | h'
      · rcases (hq.dvd_mul).1 h' with h' | h'
        · rcases (hq.dvd_mul).1 h' with h' | h'
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1
              (hq.dvd_of_dvd_pow h'))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1
              (hq.dvd_of_dvd_pow h')))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1
          (hq.dvd_of_dvd_pow h')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h'))))
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact hq2 rfl
  · exact hq3 rfl
  · norm_num at h
  · exact hq7 rfl
  · norm_num at h

theorem s168e3_pRank_lt_two_of_z7_six [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsElemAbelianOfRank 7 1 ↥L)
    (hWL : commSub ⊤ L = ⊤) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) :
    CFSG.Open.pRank q A < 2 := by
  by_contra hge
  push Not at hge
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt A
  have h1 : q ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow q hge
  have h2 : Nat.card E ∣ Nat.card A := Subgroup.card_dvd_of_le hEA
  have h3 : Nat.card A ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card A
  have h4 : Nat.card (MulAut W) ∣ Nat.card (GL (Fin 6) (ZMod 2)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
      (fun a b => mul_comm a b) hW hcard
  rw [s168e3_cyc_card_GL_six] at h4
  exact s168e3_cyc_not_sq_dvd_GL_six hq hq2 hq3 hq7 (h1.trans (h2.trans (h3.trans h4)))

end SevenSix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
