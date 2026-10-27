module

public import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Defs
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG
open CFSG.Assembly.RankThreeEven (projSL projSU)
open scoped MatrixGroups

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_mul_card_PSL2 (hp2 : p ≠ 2) :
    2 * Nat.card PSL(2, ZMod p) = p * (p ^ 2 - 1) := by
  rw [mul_comm, card_PSL2_mul_two hp2, Sec4.Census.card_SL2]

theorem mul_sq_sub_one_le {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem mul_sq_sub_one_ne {a N : ℕ} (m : ℕ) (h1 : a * (a ^ 2 - 1) < N)
    (h2 : N < (a + 1) * ((a + 1) ^ 2 - 1)) : m * (m ^ 2 - 1) ≠ N := by
  intro h
  rcases le_or_gt m a with hm | hm
  · have := mul_sq_sub_one_le hm
    omega
  · have := mul_sq_sub_one_le (show a + 1 ≤ m from hm)
    omega

theorem isEmpty_mulEquiv_PSL2_of_card {X : Type*} [Group X] {N : ℕ} (hp2 : p ≠ 2)
    (hX : Nat.card X = N) (hne : p * (p ^ 2 - 1) ≠ 2 * N) :
    IsEmpty (PSL(2, ZMod p) ≃* X) := by
  refine ⟨fun e => hne ?_⟩
  rw [← two_mul_card_PSL2 hp2, Nat.card_congr e.toEquiv, hX]

theorem card_projSL_three_seven [Fact (Nat.Prime 7)] :
    Nat.card (projSL 3 (GaloisField 7 1)) = 1876896 := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
  rw [GaloisField.card 7 1 (by norm_num)] at h
  norm_num at h
  omega

theorem not_isoLThreePi_PSL2_eight (hp5 : 5 < p) {n : ℕ} (hn : 1 ≤ n) :
    ¬ Sec4.IsoLThreePi PSL(2, ZMod p) 2 (3 * n) := by
  intro hiso
  have hcard := two_mul_card_PSL2 (p := p) (by omega)
  set q := 2 ^ (3 * n) with hq
  have hq8 : 8 ≤ q := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨g, R, hg3, hR, hM⟩ : ∃ g R : ℕ, g ∣ 3 ∧ R ≤ q ^ 2 * (q ^ 3 + 1) ∧
      Nat.card PSL(2, ZMod p) * g = q ^ 3 * R := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 (3 * n))
      rw [GaloisField.card 2 (3 * n) (by omega), ← Nat.card_congr φ.toEquiv] at h
      exact ⟨_, _, Nat.gcd_dvd_left _ _,
        Nat.mul_le_mul (Nat.sub_le _ _) ((Nat.sub_le _ _).trans (Nat.le_succ _)), h⟩
    · have h := KFacts.KS14.card_projSU_three_mul_gcd 2 (3 * n) (by omega)
      rw [← Nat.card_congr φ.toEquiv] at h
      exact ⟨_, _, Nat.gcd_dvd_left _ _, Nat.mul_le_mul (Nat.sub_le _ _) le_rfl, h⟩
  have hg1 : 1 ≤ g := Nat.pos_of_dvd_of_pos hg3 (by norm_num)
  set M := Nat.card PSL(2, ZMod p) with hMdef
  obtain ⟨a, ha⟩ := hp.out.odd_of_ne_two (by omega)
  have ha3 : 3 ≤ a := by omega
  have hsq : p ^ 2 - 1 = 4 * (a * (a + 1)) := by
    rw [ha]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hM2 : M = 2 * (p * (a * (a + 1))) := by
    rw [hsq] at hcard
    have h4 : p * (4 * (a * (a + 1))) = 2 * (2 * (p * (a * (a + 1)))) := by ring
    omega
  have hq3 : q ^ 3 = 2 ^ (9 * n) := by
    rw [hq, ← pow_mul]
    ring_nf
  have hdvdM : q ^ 3 ∣ M := by
    have h1 : q ^ 3 ∣ M * g := ⟨R, hM⟩
    have hcop : Nat.Coprime (q ^ 3) g := by
      refine Nat.Coprime.coprime_dvd_right hg3 ?_
      rw [hq3]
      exact Nat.Coprime.pow_left _ (by norm_num)
    exact hcop.dvd_of_dvd_mul_right h1
  set k := 9 * n - 1 with hkdef
  have hk : 2 ^ (9 * n) = 2 * 2 ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  have hdvd2 : 2 ^ k ∣ a * (a + 1) := by
    rw [hM2, hq3, hk] at hdvdM
    have h1 : 2 ^ k ∣ p * (a * (a + 1)) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvdM
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp.out).mpr (by omega))
    exact hcop.dvd_of_dvd_mul_left h1
  have hle : 2 ^ k ≤ a + 1 := by
    rcases Nat.even_or_odd a with ha' | ha'
    · have hodd : Odd (a + 1) := ha'.add_one
      have hcop : Nat.Coprime (2 ^ k) (a + 1) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
      exact (Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdvd2)).trans (Nat.le_succ a)
    · have hcop : Nat.Coprime (2 ^ k) a := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ha')
      exact Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_left hdvd2)
  have hQ : q ^ 3 ≤ 2 * (a + 1) := by
    rw [hq3, hk]
    omega
  have h8q : 8 * q ^ 2 ≤ q ^ 3 := by
    calc 8 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq8
      _ = q ^ 3 := by ring
  have hbig : 8 * M ≤ (2 * (a + 1)) * (2 * (a + 1)) * (2 * (a + 1) + 1) := by
    calc 8 * M ≤ 8 * (M * g) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right M hg1)
      _ = 8 * (q ^ 3 * R) := by rw [hM]
      _ ≤ 8 * (q ^ 3 * (q ^ 2 * (q ^ 3 + 1))) := by gcongr
      _ = q ^ 3 * (8 * q ^ 2) * (q ^ 3 + 1) := by ring
      _ ≤ q ^ 3 * q ^ 3 * (q ^ 3 + 1) := by gcongr
      _ ≤ (2 * (a + 1)) * (2 * (a + 1)) * (2 * (a + 1) + 1) := by gcongr
  rw [hM2, ha] at hbig
  nlinarith

theorem kSL2pNotList148 : KSL2pNotList148 := by
  intro p _ hp5
  have hp2 : p ≠ 2 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, fun n hn => not_isoLThreePi_PSL2_eight hp5 hn⟩
  · exact isEmpty_mulEquiv_PSL2_of_card hp2 KFacts.KS14.card_nativeJ2
      (mul_sq_sub_one_ne (a := 106) p (by norm_num) (by norm_num))
  · refine isEmpty_mulEquiv_PSL2_of_card hp2
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1 ?_
    have h6 := mul_sq_sub_one_le (show 6 ≤ p by omega)
    norm_num at h6 ⊢
    omega
  · exact isEmpty_mulEquiv_PSL2_of_card hp2
      KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
      (mul_sq_sub_one_ne (a := 17) p (by norm_num) (by norm_num))
  · exact isEmpty_mulEquiv_PSL2_of_card hp2
      KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2
      (mul_sq_sub_one_ne (a := 153) p (by norm_num) (by norm_num))
  · intro _
    exact isEmpty_mulEquiv_PSL2_of_card hp2 card_projSL_three_seven
      (mul_sq_sub_one_ne (a := 155) p (by norm_num) (by norm_num))

end CFSG.RankThree.PartTwo.Sec15
