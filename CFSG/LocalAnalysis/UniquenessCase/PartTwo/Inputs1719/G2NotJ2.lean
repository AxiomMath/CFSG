module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem not_isSpor_J2_of_isSp4 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsSp4 X n) : ¬ IsSpor X .J2 := by
  intro hJ2
  obtain ⟨e⟩ := hJ2
  have hcardJ2 : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  have hmodel : StatedClassicalModel X .PSp 2 2 n :=
    (show LieModel X .PSp 2 2 n from h).statedClassicalModel (by decide)
  have hX := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.1 rfl
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have hodd := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one
      (f := n) (n := 1) (by omega) le_rfl
    rw [pow_one] at hodd
    exact (Nat.coprime_two_left).mpr hodd
  rw [ordBC, hI, Finset.prod_pair (by norm_num), hg, Nat.div_one, mul_one,
    show 2 * 2 = 4 by norm_num] at hX
  have hdvd : 2 ^ (4 * n) ∣ Nat.card X := by
    rw [hX]
    have hpow : (2 ^ n) ^ 4 = 2 ^ (4 * n) := by rw [← pow_mul, mul_comm]
    rw [hpow]
    exact dvd_mul_right _ _
  have h8 : 2 ^ 8 ∣ Nat.card X :=
    (pow_dvd_pow 2 (by omega : 8 ≤ 4 * n)).trans hdvd
  rw [hcardJ2] at h8
  norm_num at h8


theorem not_isSpor_J2_of_isG2 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsG2 X n) : ¬ IsSpor X .J2 := by
  intro hJ2
  obtain ⟨e⟩ := hJ2
  have hcardJ2 : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel (show LieModel X .G2 0 2 n from h)
      (by decide)
  have hcardG2 : Nat.card X = CFSG.Open.ordG2 (2 ^ n) :=
    CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hCE.2
  have hdvd : 2 ^ (6 * n) ∣ Nat.card X := by
    rw [hcardG2]
    unfold CFSG.Open.ordG2
    have hpow : (2 ^ n) ^ 6 = 2 ^ (6 * n) := by rw [← pow_mul, mul_comm]
    rw [hpow]
    exact dvd_mul_of_dvd_left (dvd_mul_right (2 ^ (6 * n)) (2 ^ (6 * n) - 1))
      (((2 ^ n) ^ 2) - 1)
  have h12 : 2 ^ 12 ∣ Nat.card X :=
    (pow_dvd_pow 2 (by omega : 12 ≤ 6 * n)).trans hdvd
  rw [hcardJ2] at h12
  norm_num at h12

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
