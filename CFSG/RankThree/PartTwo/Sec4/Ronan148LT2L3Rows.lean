module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2L3
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Syl
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LE27Four

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.Open (StatedSL StatedSU)
open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.DFT

section SL3

theorem card_SL3_eq {q a m : ℕ} (hq2 : 2 ≤ q) (hm : ¬ 3 ∣ m) (hqm : q - 1 = 3 ^ (a + 1) * m) :
    ∃ k, ¬ 3 ∣ k ∧ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 3 ^ (2 * (a + 1) + 1) * k := by
  obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ a * m := ⟨_, rfl⟩
  have hqB : q = 3 * B + 1 := by
    have : q - 1 = 3 * B := by rw [hqm, hB, pow_succ]; ring
    omega
  have hq3 : q % 3 = 1 := by omega
  refine ⟨m ^ 2 * (q ^ 3 * (q + 1) * (3 * B * (B + 1) + 1)), ?_, ?_⟩
  · exact not_three_dvd_mul (not_three_dvd_pow 2 hm) (not_three_dvd_mul (not_three_dvd_mul
      (not_three_dvd_pow 3 (by omega)) (by omega)) (by rw [mul_assoc]; omega))
  · have h27 : 3 ^ (2 * (a + 1) + 1) * m ^ 2 = 27 * B ^ 2 := by rw [hB]; ring
    have hR : 3 ^ (2 * (a + 1) + 1) * (m ^ 2 * (q ^ 3 * (q + 1) * (3 * B * (B + 1) + 1))) =
        27 * B ^ 2 * (q ^ 3 * (q + 1) * (3 * B * (B + 1) + 1)) := by rw [← mul_assoc, h27]
    rw [hR]
    have e2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [e2, e3]
    rw [hqB]
    push_cast
    ring

variable {p e : ℕ} [Fact p.Prime]

theorem noCQ425_projSL3_mod_one (he : 1 ≤ e) (hq : p ^ e % 3 = 1) :
    NoCQ425 (projSL 3 (GaloisField p e)) := by
  have hcardF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hq2 : 2 ≤ p ^ e := by
    have := Nat.one_lt_pow (by omega : e ≠ 0) (Fact.out : p.Prime).one_lt
    omega
  obtain ⟨a, m, hm, hqm⟩ := exists_three_pow_succ (n := p ^ e - 1) (by omega) (by omega)
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd (F := GaloisField p e) (d := 3 ^ (a + 1)) (by
    rw [hcardF, hqm]
    exact Dvd.intro m rfl)
  obtain ⟨k, hk, hcard⟩ := card_SL3_eq hq2 hm hqm
  rw [← CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 3 (GaloisField p e)]
  refine noCQ425_projImage_three le_rfl hζ (fun t _ ht => ?_) ?_ ?_ hk
  · refine CFSG.Open.StatedAPI.mem_statedSL_of_det ?_
    rw [TauCeti.diagGL_coe, det_diagonal, Fin.prod_univ_three]
    have := congrArg (fun u : (GaloisField p e)ˣ => (u : GaloisField p e)) ht
    simpa using this
  · exact CFSG.Open.StatedAPI.mem_statedSL_of_det (by rw [coe_permGL3]; exact det_permMat3)
  · rw [CFSG.Open.StatedAPI.card_statedSL_three, hcardF]
    exact hcard

end SL3

section SU3

theorem card_SU3_eq {q a m : ℕ} (hm : ¬ 3 ∣ m) (hqm : q + 1 = 3 ^ (a + 1) * m) :
    ∃ k, ¬ 3 ∣ k ∧ (q : ℤ) ^ 3 * (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1)) =
      ((3 ^ (2 * (a + 1) + 1) * k : ℕ) : ℤ) := by
  obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ a * m := ⟨_, rfl⟩
  have hqB : q + 1 = 3 * B := by rw [hqm, hB, pow_succ]; ring
  have hB1 : 1 ≤ B := by omega
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      omega
    · exact h
  have hq3 : q % 3 = 2 := by omega
  refine ⟨m ^ 2 * (q ^ 3 * (q - 1) * (3 * B * (B - 1) + 1)), ?_, ?_⟩
  · exact not_three_dvd_mul (not_three_dvd_pow 2 hm) (not_three_dvd_mul (not_three_dvd_mul
      (not_three_dvd_pow 3 (by omega)) (by omega)) (by rw [mul_assoc]; omega))
  · have h27 : 3 ^ (2 * (a + 1) + 1) * m ^ 2 = 27 * B ^ 2 := by rw [hB]; ring
    have hR : 3 ^ (2 * (a + 1) + 1) * (m ^ 2 * (q ^ 3 * (q - 1) * (3 * B * (B - 1) + 1))) =
        27 * B ^ 2 * (q ^ 3 * (q - 1) * (3 * B * (B - 1) + 1)) := by rw [← mul_assoc, h27]
    rw [hR]
    have hZ : (q : ℤ) = 3 * (B : ℤ) - 1 := by
      have : ((q + 1 : ℕ) : ℤ) = ((3 * B : ℕ) : ℤ) := by rw [hqB]
      push_cast at this
      linear_combination this
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hB1]
    rw [hZ]
    ring

variable {p e : ℕ} [Fact p.Prime]

theorem unitary_diagGL_q {F : Type} [Field F] {q : ℕ} (hq : q ≠ 0) (t : Fin 3 → Fˣ)
    (ht : ∀ i, t i ^ q * t i = 1) :
    (((TauCeti.diagGL t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
      (TauCeti.diagGL t : GL (Fin 3) F) = 1 := by
  rw [TauCeti.diagGL_coe, diagonal_map (f := fun x : F => x ^ q) (zero_pow hq),
    diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ht i, Units.val_one]

theorem unitary_permGL3_q {F : Type} [Field F] {q : ℕ} (hq : q ≠ 0) :
    (((permGL3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
      (permGL3 : GL (Fin 3) F) = 1 := by
  rw [coe_permGL3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat3, Matrix.mul_apply, Fin.sum_univ_three, hq]

theorem noCQ425_projSU3_mod_two (he : 1 ≤ e) (hq : p ^ e % 3 = 2) :
    NoCQ425 (projSU 3 p e) := by
  have hU := unitaryFieldData_galoisField p e he
  have hcardF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm e 2]
  have hq0 : p ^ e ≠ 0 := pow_ne_zero e (Fact.out : p.Prime).ne_zero
  obtain ⟨a, m, hm, hqm⟩ := exists_three_pow_succ (n := p ^ e + 1) (by omega) (by omega)
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd (F := GaloisField p (2 * e)) (d := 3 ^ (a + 1)) (by
    rw [hcardF, show (p ^ e) ^ 2 - 1 = (p ^ e - 1) * (p ^ e + 1) by
      have : 1 ≤ p ^ e := Nat.one_le_iff_ne_zero.mpr hq0
      zify [this, Nat.one_le_pow 2 (p ^ e) (by omega)]
      ring, hqm]
    exact Dvd.dvd.mul_left (Dvd.intro m rfl) _)
  obtain ⟨k, hk, hcard⟩ := card_SU3_eq hm hqm
  rw [← CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 p e]
  refine noCQ425_projImage_three (CFSG.Open.StatedAPI.statedSU_le_statedSL 3 (p ^ e) _) hζ
    (fun t ht hprod => ?_) ?_ ?_ hk
  · refine Subgroup.subset_closure ⟨?_, unitary_diagGL_q hq0 t fun i => ?_⟩
    · rw [TauCeti.diagGL_coe, det_diagonal, Fin.prod_univ_three]
      have := congrArg (fun u : (GaloisField p (2 * e))ˣ => (u : GaloisField p (2 * e))) hprod
      simpa using this
    · rw [← pow_succ, hqm, pow_mul, ht i, one_pow]
  · exact Subgroup.subset_closure ⟨by rw [coe_permGL3]; exact det_permMat3,
      unitary_permGL3_q hq0⟩
  · have h := CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.card_statedSU_eq_int hU (n := 3)
      (by norm_num)
    have e3 : Finset.Icc 2 3 = {2, 3} := by decide
    rw [e3] at h
    apply Int.ofNat.inj
    change (Nat.card (StatedSU 3 (p ^ e) (GaloisField p (2 * e))) : ℤ) =
      ((3 ^ (2 * (a + 1) + 1) * k : ℕ) : ℤ)
    rw [h, ← hcard]
    simp

end SU3

section Rows


theorem kT2_two_SL_mod_one (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hq : p ^ e % 3 = 1) :
    RowOf425 (projSL 3 (GaloisField p e)) :=
  rowOf425_of_noCQ' (noCQ425_projSL3_mod_one he hq)

theorem kT2_two_SU_mod_two (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hq : p ^ e % 3 = 2) :
    RowOf425 (projSU 3 p e) :=
  rowOf425_of_noCQ' (noCQ425_projSU3_mod_two he hq)

theorem pow_mod_three_ne_zero {p e : ℕ} [Fact p.Prime] (hp : 3 < p) : p ^ e % 3 ≠ 0 := by
  intro h
  have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h)
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h3 with h' | h' <;> omega

theorem kT2_two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2) :
    RowOf425 (projSL 3 (GaloisField p e)) := by
  have h0 := pow_mod_three_ne_zero (e := e) hp
  rcases (by omega : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2) with h | h
  · exact kT2_two_SL_mod_one p e he h
  · exact kT2_two_SL_mod_two p e he h

theorem kT2_two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2) :
    RowOf425 (projSU 3 p e) := by
  have h0 := pow_mod_three_ne_zero (e := e) hp
  rcases (by omega : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2) with h | h
  · exact kT2_two_SU_mod_one p e he h
  · exact kT2_two_SU_mod_two p e he h

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
