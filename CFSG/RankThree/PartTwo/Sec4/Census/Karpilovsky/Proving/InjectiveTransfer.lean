module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.SubgroupTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.SporadicPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG.AGLEmbedding (KernelTrivialAt)

theorem kernelTrivialAt_of_injective {S T : Type} [Group S] [Group T] [Finite T]
    [Group.IsPerfect S] {p : ℕ} [Fact p.Prime] (f : S →* T) (hf : Function.Injective f)
    (hidx : ¬ p ∣ Nat.card T / Nat.card S) (h : KernelTrivialAt S p) :
    KernelTrivialAt T p := by
  have : Finite S := Finite.of_injective f hf
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  let e : S ≃* f.range := MonoidHom.ofInjective hf
  have hS : 0 < Nat.card S := Nat.card_pos
  have hHcard : Nat.card S * f.range.index = Nat.card T := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.card_mul_index f.range
  have hindex : f.range.index = Nat.card T / Nat.card S := by
    rw [← hHcard, Nat.mul_div_cancel_left _ hS]
  have hH : ¬ p ∣ f.range.index := by
    rw [hindex]
    exact hidx
  have hM : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier f.range) := by
    rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv
      e.symm]
    exact (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.kernelTrivialAt_iff_not_dvd_card_hopfMultiplier).1 h
  exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.kernelTrivialAt_of_subgroup
    f.range inferInstance hH hM

theorem kernelTrivialAt_three_B_of_fi23
    (f : CFSG.Blueprint.NativeSporadic.Carrier .Fi23 →* CFSG.Blueprint.NativeSporadic.Carrier .B)
    (hf : Function.Injective f)
    (h : KernelTrivialAt (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) 3) :
    KernelTrivialAt (CFSG.Blueprint.NativeSporadic.Carrier .B) 3 := by
  have hF : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  have hB : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .B) = CFSG.Open.monsterBabyOrder :=
    CFSG.Monster.Existence.card_nativeB
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) :=
    CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  have hnp : ¬ (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi23)).Prime :=
    not_prime_card_of_even_gt_two CFSG.Sporadic.Fi23.card_Fi23 (by norm_num) (by norm_num)
  have : Group.IsPerfect (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) :=
    isPerfect_of_simple_not_prime_card _ hnp
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .B) :=
    Nat.finite_of_card_ne_zero (by rw [hB]; norm_num [CFSG.Open.monsterBabyOrder])
  refine kernelTrivialAt_of_injective f hf ?_ h
  rw [hF, hB]
  norm_num [CFSG.Open.monsterBabyOrder, Nat.dvd_iff_mod_eq_zero]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving
