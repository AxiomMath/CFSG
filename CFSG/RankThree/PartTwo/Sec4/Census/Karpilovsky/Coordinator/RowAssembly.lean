module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.SporadicTable
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.TwoUpper
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.TwoPartTable

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.AGLEmbedding Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

section Cells

variable {X : Type} [Group X] [Finite X] [Group.IsPerfect X]

theorem primaryCentralKernelOrder_of_bounds {p k : ℕ} [hp : Fact p.Prime]
    (hup : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* X),
      Function.Surjective π → π.ker ≤ center E → IsPGroup p π.ker → Nat.card π.ker ∣ p ^ k)
    (hlow : p ^ k ∣ Nat.card (hopfMultiplier X)) : PrimaryCentralKernelOrder X p k := by
  have : Finite (hopfMultiplier X) := finite_hopfMultiplier inferInstance
  have hM : Nat.card (hopfMultiplier X) ≠ 0 := Nat.card_pos.ne'
  refine primaryCentralKernelOrder_iff.2 (le_antisymm ?_
    ((hp.out.pow_dvd_iff_le_factorization hM).1 hlow))
  obtain ⟨E, _, _, _, π, hπ, hC, hpg, hcard⟩ :=
    exists_perfect_central_pCover_card_ker_eq_primary_part (X := X) p
  have h := hup E π hπ hC hpg
  rw [hcard] at h
  exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h

theorem primaryCentralKernelOrder_zero_of_kernelTrivialAt {p : ℕ} [Fact p.Prime]
    (h : KernelTrivialAt X p) : PrimaryCentralKernelOrder X p 0 :=
  primaryCentralKernelOrder_iff.2
    (Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_hopfMultiplier_of_kernelTrivialAt h))

end Cells

theorem twoCell_of_rowBound {s : TauCeti.SporadicName} [Finite (NativeSporadic.Carrier s)]
    [IsSimpleGroup (NativeSporadic.Carrier s)] [Group.IsPerfect (NativeSporadic.Carrier s)]
    (hnc : ∃ a b : NativeSporadic.Carrier s, a * b ≠ b * a)
    (hrow : CFSG.EvenSporadicStandard.RowBound s)
    (hlow : 2 ^ (sporadicMultiplierOrder s).factorization 2 ∣
      Nat.card (hopfMultiplier (NativeSporadic.Carrier s))) :
    PrimaryCentralKernelOrder (NativeSporadic.Carrier s) 2
      ((sporadicMultiplierOrder s).factorization 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine primaryCentralKernelOrder_of_bounds (fun E _ _ _ π hπ hC hpg => ?_) hlow
  rw [← Karpilovsky.Proving.twoPartBound_eq_two_pow_factorization]
  exact Karpilovsky.Proving.twoUpper_of_rowBound s hnc hrow E π hπ hC hpg

theorem nativeRow_of_parts {s : TauCeti.SporadicName} [Finite (NativeSporadic.Carrier s)]
    [IsSimpleGroup (NativeSporadic.Carrier s)] [Group.IsPerfect (NativeSporadic.Carrier s)]
    (hnc : ∃ a b : NativeSporadic.Carrier s, a * b ≠ b * a)
    (hrow : CFSG.EvenSporadicStandard.RowBound s)
    (hlow : 2 ^ (sporadicMultiplierOrder s).factorization 2 ∣
      Nat.card (hopfMultiplier (NativeSporadic.Carrier s)))
    (h3 : PrimaryCentralKernelOrder (NativeSporadic.Carrier s) 3
      ((sporadicMultiplierOrder s).factorization 3))
    (hbig : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (NativeSporadic.Carrier s) →
      KernelTrivialAt (NativeSporadic.Carrier s) p) :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier s)) = sporadicMultiplierOrder s :=
  nativeRow_of_cells ⟨twoCell_of_rowBound hnc hrow hlow, h3, hbig⟩

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
