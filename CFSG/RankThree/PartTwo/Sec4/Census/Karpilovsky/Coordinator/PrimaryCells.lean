module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.HopfPrimaryBridge
public import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open Subgroup CFSG.RankThree.PerfectCover
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

section Multiplier

variable {X : Type} [Group X] [Finite X] [Group.IsPerfect X]

theorem dvd_card_of_dvd_card_hopfMultiplier {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card (hopfMultiplier X)) : p ∣ Nat.card X := by
  have : Finite (HopfCover X) := finite_hopfCover inferInstance
  have : Group.IsPerfect (HopfCover X) := hopfCover_isPerfect
  have hU : p ∣ Nat.card (HopfCover X) := h.trans (Subgroup.card_subgroup_dvd_card _)
  have hZ : p ∣ (center (HopfCover X)).index := by
    by_contra hn
    exact perfect_central_quotient_prime_support hp hn hU
  have h1 : (center (HopfCover X)).index ∣ (hopfMultiplier X).index :=
    Subgroup.index_dvd_of_le hopfMultiplier_le_center
  have h2 : (hopfMultiplier X).index = Nat.card X :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (hopfCoverMap_surjective (S := X))).toEquiv
  exact hZ.trans (h2 ▸ h1)

theorem primaryCentralKernelOrder_zero_of_not_dvd {p : ℕ} [Fact p.Prime]
    (h : ¬ p ∣ Nat.card X) : PrimaryCentralKernelOrder X p 0 := by
  refine primaryCentralKernelOrder_iff.2 (Nat.factorization_eq_zero_of_not_dvd fun hd => h ?_)
  exact dvd_card_of_dvd_card_hopfMultiplier Fact.out hd

theorem card_hopfMultiplier_eq_of_cells {n : ℕ} (hn : n ≠ 0)
    (hnX : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ Nat.card X)
    (h : ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card X →
      PrimaryCentralKernelOrder X p (n.factorization p)) :
    Nat.card (hopfMultiplier X) = n := by
  refine card_hopfMultiplier_eq_of_primaryCentralKernelOrder hn fun p hp => ?_
  by_cases hpX : p ∣ Nat.card X
  · exact h p hpX
  · rw [Nat.factorization_eq_zero_of_not_dvd fun hd => hpX (hnX p hp.out hd)]
    exact primaryCentralKernelOrder_zero_of_not_dvd hpX

end Multiplier

theorem card_hopfMultiplier_eq_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (hopfMultiplier X) = Nat.card (hopfMultiplier Y) :=
  Nat.card_congr ((hopfMultiplierEquivGriess X).symm.trans
    ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).trans
      (hopfMultiplierEquivGriess Y))).toEquiv

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
