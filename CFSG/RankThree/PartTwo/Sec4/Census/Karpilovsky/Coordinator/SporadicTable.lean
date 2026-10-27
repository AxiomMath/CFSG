module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.AGLEmbedding
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

@[expose] def NativeSporadicMultipliers : Prop :=
  ∀ s : TauCeti.SporadicName,
    Nat.card (hopfMultiplier (NativeSporadic.Carrier s)) = sporadicMultiplierOrder s

theorem sporadicMultiplierOrder_dvd_twelve (s : TauCeti.SporadicName) :
    sporadicMultiplierOrder s ∣ 12 := by
  cases s <;> decide

theorem sporadicMultiplierOrder_ne_zero (s : TauCeti.SporadicName) :
    sporadicMultiplierOrder s ≠ 0 := by
  cases s <;> decide

theorem not_dvd_sporadicMultiplierOrder {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (s : TauCeti.SporadicName) : ¬ p ∣ sporadicMultiplierOrder s := by
  intro hd
  have h12 := hd.trans (sporadicMultiplierOrder_dvd_twelve s)
  have hle := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> revert hp h12 <;> decide

theorem sporadicMultipliers_of_native
    (h : NativeSporadicMultipliers) : SporadicMultipliers := by
  refine ⟨fun s => ?_, h .ONan⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact (card_hopfMultiplier_eq_of_mulEquiv e).symm.trans (h s)

structure NativeRowCells (s : TauCeti.SporadicName) : Prop where
  two : PrimaryCentralKernelOrder (NativeSporadic.Carrier s) 2
    ((sporadicMultiplierOrder s).factorization 2)
  three : PrimaryCentralKernelOrder (NativeSporadic.Carrier s) 3
    ((sporadicMultiplierOrder s).factorization 3)
  big : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (NativeSporadic.Carrier s) →
    KernelTrivialAt (NativeSporadic.Carrier s) p

theorem nativeRow_of_cells {s : TauCeti.SporadicName} [Finite (NativeSporadic.Carrier s)]
    [Group.IsPerfect (NativeSporadic.Carrier s)] (h : NativeRowCells s) :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier s)) = sporadicMultiplierOrder s := by
  refine card_hopfMultiplier_eq_of_primaryCentralKernelOrder (sporadicMultiplierOrder_ne_zero s)
    fun p hp => ?_
  have hp' : p.Prime := hp.out
  by_cases h2 : p = 2
  · subst h2
    exact h.two
  by_cases h3 : p = 3
  · subst h3
    exact h.three
  have h5 : 5 ≤ p := by
    have := hp'.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp'
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd (not_dvd_sporadicMultiplierOrder hp' h5 s)]
  by_cases hpX : p ∣ Nat.card (NativeSporadic.Carrier s)
  · exact primaryCentralKernelOrder_iff.2 (Nat.factorization_eq_zero_of_not_dvd
      (not_dvd_card_hopfMultiplier_of_kernelTrivialAt (h.big p hp' h5 hpX)))
  · exact primaryCentralKernelOrder_zero_of_not_dvd hpX

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
