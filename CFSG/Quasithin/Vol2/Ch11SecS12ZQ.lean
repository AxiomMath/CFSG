module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

@[expose] def FactJ4Multiplier : Prop :=
  ¬ 3 ∣ Nat.card
    (CFSG.RankThree.PerfectCover.hopfMultiplier (CFSG.RankThree.PartTwo.Sec4.Spor .J4))

end CFSG.Quasithin.Vol2.Ch11.SecS

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

theorem cfsgQuasisimple_of_gw {Q : Type*} [Group Q]
    (h : CFSG.GorensteinWalter.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  obtain ⟨hnt, hcomm, hs⟩ := h
  refine ⟨Group.isPerfect_def.mpr hcomm, hs, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center Q), _root_.commutator_def,
      ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, eq_bot_iff]
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, b, -, rfl⟩ := hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx
  rw [hcomm] at hle
  have htriv : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff]
    exact hle trivial
  obtain ⟨a, b, hne⟩ := hs.exists_pair_ne
  exact hne ((htriv a).trans (htriv b).symm)

theorem not_three_dvd_card_center_of_J4 (hJ4M : SecS.FactJ4Multiplier)
    {K : Type} [Group K] [Finite K] (hK : CFSG.GorensteinWalter.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* CFSG.RankThree.PartTwo.Sec4.Spor .J4) :
    ¬ 3 ∣ Nat.card (Subgroup.center K) := fun h3 =>
  hJ4M (h3.trans (CFSG.GH74.Generic.card_center_dvd_hopfMultiplier (cfsgQuasisimple_of_gw hK) e))

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
