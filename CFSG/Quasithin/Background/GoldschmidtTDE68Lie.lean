module

public import CFSG.Quasithin.Background.GoldschmidtTDE68CovBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.GH74.KGroups.A6
public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.Quasithin.E6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.ComponentClassification.CatLeaf
  CFSG.Assembly.LowTwoRank

theorem involutionCentralizersComponentFree_of_sqtkCharTwoLie
    {X : Type} [Group X] (h : SQTKCharTwoLie X) : InvolutionCentralizersComponentFree X := by
  rcases h with ((⟨f, h | h | h | h | h | h | h | h⟩ | h) | ⟨n, -, h⟩)
  · exact involutionCentralizersComponentFree_psl h.2
  · exact involutionCentralizersComponentFree_psl h.2
  · exact involutionCentralizersComponentFree_psu h.2
  · exact involutionCentralizersComponentFree_psp h.2
  · exact involutionCentralizersComponentFree_exceptional (t := .G2)
      (by simp [CFSG.Blueprint.chevalleyExceptionalTags]) h.2
  · exact involutionCentralizersComponentFree_exceptional (t := .trialityD4)
      (by simp [CFSG.Blueprint.chevalleyExceptionalTags]) h.2
  · exact involutionCentralizersComponentFree_reeTits (.inl rfl) h.2.2
  · exact involutionCentralizersComponentFree_suzuki h.2.2
  · exact involutionCentralizersComponentFree_reeTits (.inr rfl) h
  · exact involutionCentralizersComponentFree_psl h

end CFSG.Quasithin.E6

namespace CFSG.Quasithin.E6

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.Ch1
  CFSG.ComponentClassification.CatLeaf CFSG.Quasithin.E6.Bar CFSG.Assembly.LowTwoRank
  CFSG.GH74.KGroups

theorem e68CentCompLie_holds : E68CentCompLie := by
  intro Y _ _ L R K z u hA h hK
  exfalso
  obtain ⟨hs, hlie, -⟩ := hA
  rcases hlie with hsq | h6 | hu33
  · have hE : EvenLieAutInner := evenLieAutInner_of_tits titsSylowCentralizingAutInner
    have hfix : Inn.InvolFixInner ↥L := by
      intro Q hQ β hβ2 hβ
      have hidx : ¬ 2 ∣ Q.index := by
        have h1 : (Q.subgroupOf ⊤).index = Q.index := Subgroup.relIndex_top_right Q
        have := hQ.2.2
        rwa [h1] at this
      exact hE ↥L hsq β hβ2 ⟨hQ.2.1.toSylow hidx, hβ⟩
    have hc : center ↥L = ⊥ := Inn.center_eq_bot_of_isQuasisimple_of_simple h.quasisimple hs
    let e : Qbar L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact Inn.not_isComponentIn_of_fix_free h (Inn.InvolFixInner.of_mulEquiv e hfix)
      (InvolutionCentralizersComponentFree.of_mulEquiv e
        (involutionCentralizersComponentFree_of_sqtkCharTwoLie hsq)) K hK
  · obtain ⟨e⟩ := A6.equiv_of_alt6 h6
    exact Inn.not_isComponentIn_of_fixed_solvable h
      (fun α h2 h1 M hM => A6.fixed_solvable e α h2 h1 M hM) K hK
  · obtain ⟨e⟩ := U33.equiv_of_lieModel (Or.inl ⟨by decide, hu33⟩)
    exact Inn.not_isComponentIn_of_fixed_solvable h
      (fun α h2 h1 M hM => U33.fixed_solvable e α h2 h1 M hM) K hK

end CFSG.Quasithin.E6
