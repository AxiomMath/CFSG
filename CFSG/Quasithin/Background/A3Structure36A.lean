
module

public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Quasithin.Background.A3Structure36AList

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace A36A

theorem a36BHyp_of_mem_cComp {G : Type} [Group G] (hG : SQTKHyp G) {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hnc : ¬ CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) :
    A36BHyp ↥L := by
  have := hG.finite
  obtain ⟨hs, hna⟩ := simple_quotient_of_mem_cComp hL
  exact
    { finite := inferInstance
      perfect := top_commutator_of_mem_cComp hL
      simple := hs
      nonabelian := hna
      o2 := hG.pCore_two_of_subnormal (subnormal_of_mem_cComp hL)
      rank := (hG.subgroup L).1
      noncentral := hnc }

theorem a36Strong_of_not_fitting_le_center (hB : A36CaseBStatement) {G : Type} [Group G]
    (hG : SQTKHyp G) {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G))
    (hnc : ¬ CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) : A36Strong L := by
  obtain ⟨h34, hcommon, hextra⟩ := hB ↥L (a36BHyp_of_mem_cComp hG hL hnc)
  exact ⟨Or.inr (Or.inr h34), hcommon, fun _ => hextra⟩

theorem a36Strong_of_fitting_le_center (hT : ThreeCoverFact) (hList : A23SQTKListFact)
    (hCat : CatalogStepFact) {G : Type} [Group G] (hG : SQTKHyp G)
    {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G))
    (hFZ : CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) : A36Strong L := by
  have := hG.finite
  obtain ⟨hs, hna⟩ := simple_quotient_of_mem_cComp hL
  have hQ : CFSG.IsQuasisimple ↥L :=
    isQuasisimple_of_fitting_le_center (isPerfect_of_mem_cComp hL) hs hna hFZ
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    odd_card_center (hG.pCore_two_of_subnormal (subnormal_of_mem_cComp hL))
  have hZ13 := hCat ↥L hQ (hG.subgroup L) hodd
  have hcomp : CFSG.IsComponent L :=
    ⟨hQ, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hL)⟩
  have hlist : A23List (↥L ⧸ Subgroup.center ↥L) :=
    hList G hG.sqtkGroup L (Subgroup.center ↥L) hQ.2.1 hQ.2.2
  refine ⟨?_, ?_, ?_⟩
  · rcases hZ13 with h1 | h3
    · refine Or.inl ⟨hcomp, ?_⟩
      have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
        (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
      have := hQ.2.1
      exact ⟨e.symm.isSimpleGroup, a23List_of_mulEquiv e.symm hlist⟩
    · exact Or.inr (Or.inl ⟨hcomp, h3, hT ↥L hQ h3 hlist⟩)
  · have hFeq : CFSG.fittingSubgroup ↥L = Subgroup.center ↥L := fittingSubgroup_eq_center hFZ
    have hReq : Subgroup.center ↥L = CFSG.solvableRadical ↥L := center_eq_solvableRadical hFZ
    have hOeq : CFSG.oddCore ↥L = Subgroup.center ↥L := oddCore_eq_center hFZ hodd
    have hRR : ⁅CFSG.solvableRadical ↥L, CFSG.solvableRadical ↥L⁆ = ⊥ := by
      rw [← hReq]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hFtop : ⁅CFSG.fittingSubgroup ↥L, (⊤ : Subgroup ↥L)⁆ = ⊥ := by
      rw [hFeq]
      exact Subgroup.commutator_center_left _
    refine ⟨hFeq.trans hOeq.symm,
      (CFSG.LocalCores.quasisimple_central_quotient hQ (CFSG.fittingSubgroup ↥L) hFZ).1,
      Or.inr ⟨hFeq, hFeq.trans hReq, ?_⟩, hRR.trans hFtop.symm,
      (CFSG.LocalCores.quasisimple_central_quotient hQ
        ⁅CFSG.solvableRadical ↥L, CFSG.solvableRadical ↥L⁆ (by rw [hRR]; exact bot_le)).1⟩
    rw [hFeq]
    exact hZ13
  · intro hc
    exfalso
    have hgf : CFSG.generalizedFitting ↥L = CFSG.fittingSubgroup ↥L := by
      rcases hc with ⟨_, _, _, h, _⟩ | ⟨h, _⟩ <;> exact h
    exact generalizedFitting_ne_fittingSubgroup hQ hFZ hgf

end A36A

theorem a36_of_caseB (hF : A36Facts) (hB : A36CaseBStatement) {G : Type} [Group G]
    (hG : SQTKHyp G) : A36Statement G := by
  intro L hL
  by_cases hnc : CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L
  · exact A36A.a36Strong_of_fitting_le_center hF.threeCover hF.list hF.catalog hG hL hnc
  · exact A36A.a36Strong_of_not_fitting_le_center hB hG hL hnc

end CFSG.Quasithin
