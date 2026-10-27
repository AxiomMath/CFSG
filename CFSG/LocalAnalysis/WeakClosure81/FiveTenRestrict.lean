module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenDefs
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenWeak

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def FiveTenDescent (H M : Subgroup G) (Ω : Set (Subgroup G)) : Prop :=
  ∃ (N T' : Subgroup G) (Ω' : Set (Subgroup G)), N < H ∧ FiveTenHyp N M T' Ω' ∧ Ω' ⊆ Ω

theorem FiveTenHyp.restrict {H N M S : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hNH : N ≤ H) (hS : IsSylowIn 2 S N)
    (hSM : H ⊓ normalizer (E1.weakClosure S Ω : Set G) ≤ M) (hNM : ¬ N ≤ M) :
    FiveTenHyp N M S {B | B ∈ Ω ∧ B ≤ N} := by
  refine ⟨isInvColl_restrict hΩ hNH, hS, ?_, hNM⟩
  rw [weakClosure_restrict hS.le]
  exact (inf_le_inf_right _ hNH).trans hSM

theorem FiveTenDescent.of_restrict {H N M S : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hNH : N < H) (hS : IsSylowIn 2 S N)
    (hSM : H ⊓ normalizer (E1.weakClosure S Ω : Set G) ≤ M) (hNM : ¬ N ≤ M) :
    FiveTenDescent H M Ω :=
  ⟨N, S, {B | B ∈ Ω ∧ B ≤ N}, hNH, FiveTenHyp.restrict hΩ hNH.le hS hSM hNM,
    fun _ hB => hB.1⟩

theorem FiveTenConc.of_le {H N M : Subgroup G} {Ω Ω' : Set (Subgroup G)} (hNH : N ≤ H)
    (hΩ : Ω' ⊆ Ω) (hker : kerMOf M H = ⊥) (h : FiveTenConc N M Ω') : FiveTenConc H M Ω := by
  obtain ⟨A, hA, hAM, H', hH'N, hAH', hk, hAk, hmax⟩ := h
  refine ⟨A, hΩ hA, hAM, H', hH'N.trans hNH, hAH', ?_, hAk, hmax⟩
  rw [hker]
  exact bot_le

end CFSG.LocalAnalysis.WeakClosure81
