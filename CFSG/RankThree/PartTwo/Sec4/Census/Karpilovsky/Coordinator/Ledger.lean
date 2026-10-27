module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.RowAssembly
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.MonsterLargePrime

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.AGLEmbedding Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving (factorization_2_two
  factorization_2_three factorization_3_two factorization_3_three factorization_6_two
  factorization_6_three)

@[expose] def CarrierFacts (s : TauCeti.SporadicName) : Prop :=
  Finite (NativeSporadic.Carrier s) ∧ IsSimpleGroup (NativeSporadic.Carrier s) ∧
    Group.IsPerfect (NativeSporadic.Carrier s) ∧
      ∃ a b : NativeSporadic.Carrier s, a * b ≠ b * a

@[expose] def BigPrimeFacts (s : TauCeti.SporadicName) : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (NativeSporadic.Carrier s) →
    KernelTrivialAt (NativeSporadic.Carrier s) p

structure SporadicOpenCells : Prop where
  fi23_three : KernelTrivialAt (NativeSporadic.Carrier .Fi23) 3

section Rows

theorem nativeRow_of_two_one_three_zero {s : TauCeti.SporadicName}
    (hs : sporadicMultiplierOrder s = 2) (hC : CarrierFacts s)
    (hrow : CFSG.EvenSporadicStandard.RowBound s)
    (hlow : 2 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier s)))
    (h3 : KernelTrivialAt (NativeSporadic.Carrier s) 3) (hB : BigPrimeFacts s) :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier s)) = sporadicMultiplierOrder s := by
  obtain ⟨hfin, hsimp, hperf, hnc⟩ := hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine nativeRow_of_parts hnc hrow ?_ ?_ hB
  · rw [hs, factorization_2_two, pow_one]
    exact hlow
  · rw [hs, factorization_2_three]
    exact primaryCentralKernelOrder_zero_of_kernelTrivialAt h3

theorem nativeRow_of_two_zero_three_one {s : TauCeti.SporadicName}
    (hs : sporadicMultiplierOrder s = 3) (hC : CarrierFacts s)
    (hrow : CFSG.EvenSporadicStandard.RowBound s)
    (h3 : PrimaryCentralKernelOrder (NativeSporadic.Carrier s) 3 1) (hB : BigPrimeFacts s) :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier s)) = sporadicMultiplierOrder s := by
  obtain ⟨hfin, hsimp, hperf, hnc⟩ := hC
  refine nativeRow_of_parts hnc hrow ?_ ?_ hB
  · rw [hs, factorization_3_two, pow_zero]
    exact one_dvd _
  · rw [hs, factorization_3_three]
    exact h3

theorem nativeRow_of_two_zero_three_zero {s : TauCeti.SporadicName}
    (hs : sporadicMultiplierOrder s = 1) (hC : CarrierFacts s)
    (hrow : CFSG.EvenSporadicStandard.RowBound s)
    (h3 : KernelTrivialAt (NativeSporadic.Carrier s) 3) (hB : BigPrimeFacts s) :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier s)) = sporadicMultiplierOrder s := by
  obtain ⟨hfin, hsimp, hperf, hnc⟩ := hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine nativeRow_of_parts hnc hrow ?_ ?_ hB
  · rw [hs, Nat.factorization_one, Finsupp.zero_apply, pow_zero]
    exact one_dvd _
  · rw [hs, Nat.factorization_one, Finsupp.zero_apply]
    exact primaryCentralKernelOrder_zero_of_kernelTrivialAt h3

theorem nativeRow_of_two_one_three_one {s : TauCeti.SporadicName}
    (hs : sporadicMultiplierOrder s = 6) (hC : CarrierFacts s)
    (hrow : CFSG.EvenSporadicStandard.RowBound s)
    (hlow : 2 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier s)))
    (h3 : PrimaryCentralKernelOrder (NativeSporadic.Carrier s) 3 1) (hB : BigPrimeFacts s) :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier s)) = sporadicMultiplierOrder s := by
  obtain ⟨hfin, hsimp, hperf, hnc⟩ := hC
  refine nativeRow_of_parts hnc hrow ?_ ?_ hB
  · rw [hs, factorization_6_two, pow_one]
    exact hlow
  · rw [hs, factorization_6_three]
    exact h3

theorem bigPrimeFacts_M (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (h5 : KernelTrivialAt (NativeSporadic.Carrier .M) 5)
    (h7 : KernelTrivialAt (NativeSporadic.Carrier .M) 7)
    (h11 : KernelTrivialAt (NativeSporadic.Carrier .M) 11)
    (h13 : KernelTrivialAt (NativeSporadic.Carrier .M) 13) : BigPrimeFacts .M := by
  intro p hp hp5 _
  have : Fact p.Prime := ⟨hp⟩
  by_cases hgt : 13 < p
  · exact kernelTrivialAt_carrier_M_of_gt_thirteen hMcard hgt
  · interval_cases p <;> first | assumption | (exfalso; revert hp; decide)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
