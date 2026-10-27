module

public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingFusionCorrBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

theorem w1369_generalizedFitting_eq_of_isComponent_of_centralizer_le
    {H : Type*} [Group H] [Finite H] (Q : Subgroup H) (hQ : CFSG.IsComponent Q)
    (hC : Subgroup.centralizer (Q : Set H) ≤ Q) : CFSG.generalizedFitting H = Q := by
  have hothers : sSup {T : Subgroup H | CFSG.IsComponent T ∧ T ≠ Q} ≤ Q := by
    refine sSup_le ?_
    rintro T ⟨hT, hTQ⟩
    have hcomm : ⁅T, Q⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hT hQ).resolve_left hTQ
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hC
  have hlayer : CFSG.layer H = Q := by
    rw [(CFSG.WholeGroup.layer_eq_sup_others hQ).2, sup_eq_left.mpr hothers]
  have hfit : CFSG.fittingSubgroup H ≤ Q := by
    have hcomm : ⁅CFSG.fittingSubgroup H, CFSG.layer H⁆ = ⊥ :=
      CFSG.LocalCores.fitting_layer_commute (G := H)
    have hcent : CFSG.fittingSubgroup H ≤ Subgroup.centralizer (Q : Set H) := by
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans ?_
      exact Subgroup.centralizer_le (by rw [hlayer])
    exact hcent.trans hC
  rw [CFSG.generalizedFitting, hlayer, sup_eq_right.mpr hfit]

theorem w1369_fstar_eq_of_centralizer_le {M : Type} [Group M] [Finite M] {Y L : Subgroup M}
    (hLY : L ≤ Y) (hN : (L.subgroupOf Y).Normal) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hC : Subgroup.centralizer (L : Set M) ⊓ Y ≤ L) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar Y = L := by
  classical
  set Q : Subgroup ↥Y := L.subgroupOf Y with hQ
  have hq' : CFSG.IsQuasisimple ↥L :=
    (CFSG.ComponentClassification.UnbalancingLocal.isQuasisimple_open_iff ↥L).mp hq
  have hQq : CFSG.IsQuasisimple Q :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLY).symm hq'
  have hQcomp : CFSG.IsComponent Q := ⟨hQq, hN.isSubnormal⟩
  have hCQ : Subgroup.centralizer (Q : Set ↥Y) ≤ Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hC ⟨?_, x.2⟩
    change (x : M) ∈ Subgroup.centralizer (L : Set M)
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro l hl
    have hqQ : (⟨l, hLY hl⟩ : ↥Y) ∈ Q := by
      rw [Subgroup.mem_subgroupOf]
      exact hl
    exact congrArg Subtype.val (hx ⟨l, hLY hl⟩ hqQ)
  have hgen : CFSG.generalizedFitting ↥Y = Q :=
    w1369_generalizedFitting_eq_of_isComponent_of_centralizer_le Q hQcomp hCQ
  change (CFSG.Open.genFittingFStar ↥Y).map Y.subtype = L
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, hgen, hQ]
  exact Subgroup.map_subgroupOf_eq_of_le hLY

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
