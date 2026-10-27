module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312Tools

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312

theorem zmod64_L3 : ∀ r : ZMod 64, (r.val % 8 = 3 ∨ r.val % 8 = 5) →
    r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) ≠ 0 := by
  decide

theorem zmod64_U3 : ∀ r : ZMod 64, (r.val % 8 = 3 ∨ r.val % 8 = 5) →
    r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) ≠ 0 := by
  decide

theorem not64_L3_nat (q : ℕ) (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ¬ 64 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  intro h
  have hq1 : 1 ≤ q := by omega
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h2 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have hc : ((q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) : ℕ) : ZMod 64) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 64) 64 _).mpr h
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hc
  apply zmod64_L3 (q : ZMod 64) _ hc
  rw [ZMod.val_natCast]
  omega

theorem not64_U3_nat (q : ℕ) (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ¬ 64 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  intro h
  have hq1 : 1 ≤ q := by omega
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hc : ((q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) : ℕ) : ZMod 64) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 64) 64 _).mpr h
  push_cast [Nat.cast_sub h1] at hc
  apply zmod64_U3 (q : ZMod 64) _ hc
  rw [ZMod.val_natCast]
  omega

theorem charP_of_card_sq (K : Type) [Field K] [Finite K] {q : ℕ} (hq : q.Prime)
    (hK : Nat.card K = q ^ 2) : CharP K q := by
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI hr : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card] at hK
  have hdvd : q ∣ (ringChar K) ^ (n : ℕ) := by
    rw [← hn, hK]
    exact dvd_pow_self q two_ne_zero
  have hqr : q = ringChar K := (Nat.prime_dvd_prime_iff_eq hq hr.out).mp (hq.dvd_of_dvd_pow hdvd)
  rw [hqr]
  exact ringChar.charP K

theorem not64_psl3 {J : Type} [Group J] [Finite J] {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5)
    (h : IsPSL 3 q 1 J) : ¬ 64 ∣ Nat.card J := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound J 3 q 1 h).1
  rw [pow_one] at hb
  have hprod : ∏ j ∈ Finset.Icc 2 3, (q ^ j - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]
  have e3 : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [hprod, e3] at hb
  have hd1 : q - 1 ∣ q ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  have hg : Nat.gcd 3 (q - 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    dvd_trans (dvd_trans (Nat.gcd_dvd_right 3 (q - 1)) hd1)
      (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  have hmul : Nat.card J * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [hb]
    exact Nat.div_mul_cancel hg
  intro h64
  apply not64_L3_nat q hq
  rw [← hmul]
  exact Dvd.dvd.mul_right h64 _


theorem not64_psu3 {J : Type} [Group J] [Finite J] {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5)
    (h : IsPSU 3 q 1 J) : ¬ 64 ∣ Nat.card J := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound J 3 q 1 h).1
  simp only [pow_one] at hb
  have hprod : ∏ j ∈ Finset.Icc 2 3, ((q : ℤ) ^ j - (-1) ^ j) =
      ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]
    norm_num
  have e3 : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [hprod, e3] at hb
  intro h64
  apply not64_U3_nat q hq
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX : ((q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) : ℕ) : ℤ) =
      (q : ℤ) ^ 3 * (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1)) := by
    push_cast [Nat.cast_sub h1]
    ring
  have hdvd : (64 : ℤ) ∣ ((q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) : ℕ) : ℤ) := by
    rw [hX, ← hb]
    exact Dvd.dvd.mul_right (by exact_mod_cast h64) _
  exact_mod_cast hdvd

theorem not64_sl3 {J : Type} [Group J] {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) (h : IsSL3 q J) :
    ¬ 64 ∣ Nat.card J := by
  obtain ⟨K, hF, hKf, hK, ⟨e⟩⟩ := h
  letI := hF
  letI := hKf
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three K, hK]
  exact not64_L3_nat q hq

theorem not64_su3 {J : Type} [Group J] {q : ℕ} (hqp : q.Prime) (hq : q % 8 = 3 ∨ q % 8 = 5)
    (h : IsSU3 q J) : ¬ 64 ∣ Nat.card J := by
  obtain ⟨K, hF, hKf, hK, ⟨e⟩⟩ := h
  letI := hF
  letI := hKf
  haveI : CharP K q := charP_of_card_sq K hqp hK
  haveI : Fact q.Prime := ⟨hqp⟩
  have hK' : Nat.card K = (q ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hc := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := q) (f := 1) hK'
  simp only [pow_one] at hc
  rw [Nat.card_congr e.toEquiv, hc, mul_assoc]
  apply not64_U3_nat q hq

theorem not64_pslEps3 {J : Type} [Group J] [Finite J] {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5)
    (s : Bool) (h : IsPSLEps3 s q 1 J) : ¬ 64 ∣ Nat.card J := by
  cases s
  · exact not64_psu3 hq h
  · exact not64_psl3 hq h

theorem not64_slEps3 {J : Type} [Group J] {q : ℕ} (hqp : q.Prime) (hq : q % 8 = 3 ∨ q % 8 = 5)
    (s : Bool) (h : IsSLEps3 s q J) : ¬ 64 ∣ Nat.card J := by
  cases s
  · exact not64_su3 hqp hq h
  · exact not64_sl3 hq h

end CFSG.Quasithin.H13.NF314ptA312
