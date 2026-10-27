module

public import CFSG.Quasithin.Background.GoldschmidtTDE68CovBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.K1
  CFSG.ComponentClassification.CatLeaf CFSG.Quasithin.E6.Bar

theorem e68CentCompCover_holds : E68CentCompCover := by
  intro Y _ _ L R K z u hB h hK
  exfalso
  obtain ⟨-, hZ, hmodel, -⟩ := hB
  let e : Qbar L ≃* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.quotientMulEquivOfEq hZ
  rcases hmodel with hpsl | hg2
  · exact Inn.not_isComponentIn_of_fix_free h
      (Inn.InvolFixInner.of_forall (SylowCentralizingAutInner.of_mulEquiv e
        (sylowCentralizingAutInner_of_stated_psl (by norm_num) (by norm_num) hpsl)))
      (InvolutionCentralizersComponentFree.of_mulEquiv e
        (involutionCentralizersComponentFree_psl hpsl)) K hK
  · exact Inn.not_isComponentIn_of_fix_free h
      (Inn.InvolFixInner.of_forall (SylowCentralizingAutInner.of_mulEquiv e
        (sylowCentralizingAutInner_of_g2_model (by norm_num) hg2)))
      (InvolutionCentralizersComponentFree.of_mulEquiv e
        (involutionCentralizersComponentFree_exceptional (t := .G2)
          (by simp [CFSG.Blueprint.chevalleyExceptionalTags]) hg2)) K hK

end CFSG.Quasithin.E6
