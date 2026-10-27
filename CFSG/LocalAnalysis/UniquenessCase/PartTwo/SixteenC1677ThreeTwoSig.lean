module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoCommon
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_two_no_sq {N : ℕ} (S : Finset ℕ) (hN : N ≠ 0)
    (hS : N.primeFactors = S) (hS' : ∀ p ∈ S, p = 2 ∨ p = 3 ∨ ¬ p ^ 2 ∣ N) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ N := by
  intro p hp hp2 hp3 h
  have hmem : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, hN⟩
  rw [hS] at hmem
  rcases hS' p hmem with h2 | h3 | h'
  · exact hp2 h2
  · exact hp3 h3
  · exact h' h

private theorem s168e3_two_not_sq_dvd_factorial_nine {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.factorial 9 := by
  intro h
  have hd : p ∣ Nat.factorial 9 := (dvd_pow_self p (by norm_num)).trans h
  have hle : p ≤ 9 := (hp.dvd_factorial).mp hd
  interval_cases p <;> (first | (norm_num at hp; done) | norm_num at h)

private theorem s168e3_two_alt_arith {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hn9 : n ≤ 9) : ¬ p ^ 2 ∣ 6 * Nat.factorial n := by
  intro h
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hcop : Nat.Coprime (p ^ 2) 6 :=
    (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) p 6).2
      (hp.coprime_iff_not_dvd.2 (by
        intro hd
        have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
        interval_cases p <;> (first | (norm_num at hp; done) | norm_num at hd)))
  exact s168e3_two_not_sq_dvd_factorial_nine hp hp5
    ((hcop.dvd_of_dvd_mul_left h).trans (Nat.factorial_dvd_factorial hn9))

private theorem s168e3_two_alt6_arith :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ 6 * (4 * 360) :=
  s168e3_two_no_sq {2, 3, 5} (by norm_num) (by simp [Nat.primeFactors]) (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num)

private theorem s168e3_two_ln_arith {N : ℕ} (h : N = 168 ∨ N = 20160 ∨ N = 9999360) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ 6 * (2 * N) := by
  rcases h with rfl | rfl | rfl
  · refine s168e3_two_no_sq {2, 3, 7} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  · refine s168e3_two_no_sq {2, 3, 5, 7} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · refine s168e3_two_no_sq {2, 3, 5, 7, 31} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem s168e3_two_sp_arith :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ 6 * 1451520 :=
  s168e3_two_no_sq {2, 3, 5, 7} (by norm_num) (by simp [Nat.primeFactors]) (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num)

private theorem s168e3_two_om_arith {N : ℕ} (h : N = 25920 ∨ N = 197406720) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ 6 * (2 * N) := by
  rcases h with rfl | rfl
  · refine s168e3_two_no_sq {2, 3, 5} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  · refine s168e3_two_no_sq {2, 3, 5, 7, 17} (by norm_num) (by simp [Nat.primeFactors]) ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem s168e3_two_alt_sig {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn5 : 5 ≤ n)
    (hn9 : n ≤ 9) (hn6 : n ≠ 6) (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) : D.sig = {3} := by
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * Nat.factorial n :=
    s16e_two_fam_alt_card_mbar D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting
      c.ne hs hn5 hn6 hA hsum
  exact s168e3_two_sig c hcard (fun p hp hp2 hp3 => s168e3_two_alt_arith hp hp2 hp3 hn9)

theorem s168e3_two_alt6_sig {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) : D.sig = {3} := by
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * (4 * 360) :=
    s16e_two_card_mbar D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs
      (s16e_two_fam_alt D hV (by norm_num : 5 ≤ 6) hA hsum) (a := 4 * 360)
      (s16e_two_alt6_card_aut_dvd hA)
  exact s168e3_two_sig c hcard s168e3_two_alt6_arith

theorem s168e3_two_ln_sig {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {m : ℕ} (hm3 : 3 ≤ m)
    (hm5 : m ≤ 5) (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) : D.sig = {3} := by
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣
      6 * (2 * Nat.card ↥(lBar V₀ V hV L)) :=
    s16e_two_fam_ln_card_mbar D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting
      c.ne hs hm3 hm5 hLm hsum
  exact s168e3_two_sig c hcard (fun p hp hp2 hp3 =>
    s168e3_two_ln_arith (s16e_two_ln_card_cases hm3 hm5 hLm) p hp hp2 hp3)

theorem s168e3_two_sp_sig {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) : D.sig = {3} := by
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * 1451520 :=
    s16e_two_fam_sp_card_mbar D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting
      c.ne hs hSp hsum
  exact s168e3_two_sig c hcard s168e3_two_sp_arith

theorem s168e3_two_om_sig {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn : n = 6 ∨ n = 8)
    (hO : IsOmegaMinus ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) : D.sig = {3} := by
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣
      6 * (2 * Nat.card ↥(lBar V₀ V hV L)) :=
    s16e_two_fam_om_card_mbar D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting
      c.ne hs hn hO hsum
  exact s168e3_two_sig c hcard (fun p hp hp2 hp3 =>
    s168e3_two_om_arith (s16e_two_om_card_cases hn hO) p hp hp2 hp3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
