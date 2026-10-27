module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
import CFSG.RankThree.PartOne.KF.U4Model
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem card_su32 {Y : Type} [Group Y] [Finite Y] (h : R891SU32 Y) :
    Nat.card Y = 216 := by
  obtain ⟨φ, hsurj, hExtra, -⟩ := h
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hExtra
  have hker : Nat.card ↥φ.ker = 3 ^ (1 + 2 * 1) := hExtra.1
  have hquot : Nat.card (Y ⧸ φ.ker) = Nat.card (QuaternionGroup 2) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have hq8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hquot, hq8, hker]
  norm_num

private theorem card_psl3_cover {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hEven : Even n)
    (h : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover (fun Z _ => LieModel Z .PSL 3 2 n) Y) :
    Nat.card Y = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1) := by
  obtain ⟨-, hcenter, hQ⟩ := h
  have hcardQ : Nat.card (Y ⧸ Subgroup.center Y) = ordA 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two (hQ.statedClassicalModel (by decide))).1 rfl
  have hcardY : Nat.card Y = Nat.card (Y ⧸ Subgroup.center Y) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), hcenter]
  have hdvd : 3 ∣ 2 ^ n - 1 := by
    obtain ⟨k, rfl⟩ := hEven
    rw [show k + k = 2 * k by omega, pow_mul]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 k
  have hgcd : Nat.gcd 3 (2 ^ n - 1) = 3 := Nat.gcd_eq_left hdvd
  have hcard := CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_two_mul_gcd (2 ^ n)
  rw [← hcardQ, hgcd] at hcard
  rw [hcardY, hcard,
    show (2 ^ n) ^ 3 = 2 ^ (3 * n) by rw [← pow_mul, mul_comm],
    show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]]
  ring

private theorem card_psu3_cover {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hOdd : Odd n)
    (h : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover (fun Z _ => LieModel Z .PSU 3 2 n) Y) :
    Nat.card Y = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
  obtain ⟨-, hcenter, hQ⟩ := h
  have hcardQ : Nat.card (Y ⧸ Subgroup.center Y) = ordTwistedA 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two (hQ.statedClassicalModel (by decide))).2.1 rfl
  have hcardY : Nat.card Y = Nat.card (Y ⧸ Subgroup.center Y) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), hcenter]
  have hdvd : 3 ∣ 2 ^ n + 1 := by
    obtain ⟨k, rfl⟩ := hOdd
    have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h1]
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 3 := Nat.gcd_eq_left hdvd
  have hcard := CFSG.RankThree.PartOne.KFU.ordTwistedA_two_mul_gcd (2 ^ n)
  rw [← hcardQ, hgcd] at hcard
  rw [hcardY, hcard,
    show (2 ^ n) ^ 3 = 2 ^ (3 * n) by rw [← pow_mul, mul_comm],
    show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]]
  ring

theorem primeCore_sl3Two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (h : R891SL3Two Y n) :
    (Nat.card Y : ℤ) = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - R891Pi n) := by
  rcases h with ⟨rfl, hSU⟩ | ⟨-, hEven, hTC⟩ | ⟨-, hOdd, hTC⟩
  · rw [card_su32 hSU]
    norm_num [R891Pi]
  · have hpi : R891Pi n = 1 := by rw [R891Pi, hEven.neg_one_pow]
    have hY := card_psl3_cover hEven hTC
    rw [hpi, hY]
    have h1 : (1 : ℕ) ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have h2 : (1 : ℕ) ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
    push_cast
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    ring
  · have hpi : R891Pi n = -1 := by rw [R891Pi, hOdd.neg_one_pow]
    have hY := card_psu3_cover hOdd hTC
    rw [hpi, hY]
    have h1 : (1 : ℕ) ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    push_cast
    rw [Nat.cast_sub h1]
    push_cast
    ring

theorem primeCore_l2 {U : Type} [Group U] [Finite U] {m : ℕ} (h : LieModel U .PSL 2 2 m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup U) ≤ 1 ∧ (p ∣ Nat.card U ↔ p ∣ 2 ^ (2 * m) - 1) := by
  refine ⟨CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_le_one_of_isL2_or_isSz
    (Or.inl h) hp hp2, ?_⟩
  have hm : 1 ≤ m := h.admissible.2.1
  have hcard : Nat.card U = 2 ^ m * (4 ^ m - 1) := by
    have hord : Nat.card U = ordA 1 (2 ^ m) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two (h.statedClassicalModel (by decide))).1 rfl
    rw [hord, CFSG.RankThree.PartOne.KFU.ordA_one_two_pow hm,
      show (2 ^ m) ^ 2 = 4 ^ m by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega]
  have h4 : 4 ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hcop : Nat.Coprime p (2 ^ m) :=
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right m
  rw [hcard, h4]
  exact hcop.dvd_mul_left

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core
