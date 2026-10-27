module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4RecogA1
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4RecogA2in
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4RecogA2out
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4RecogB2
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Shapes
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Orbit
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AR
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
import CFSG.Blueprint.OddStandardExact

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieSmallFormA8Plane3_F4
    :
    GGLieSmallFormA8Plane3 .F4 := by
  intro L _ _ _ D ρ hρ hfin hq a₁ a₂ h₁ h₂ hp₁ hp₂ hcard i hR hA3
  exfalso
  have hH : GGLieF4PlaneHyp D ρ a₁ a₂ := ⟨hρ, hfin, hq, h₁, h₂, hp₁, hp₂, hcard⟩
  obtain ⟨f, hf, hqf⟩ := hq
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hc := CFSG.OddStandard.HigherRank.YamadaG23.y6f4a_card_psl_four_two hO hA3
  have hsolv := CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hR
  have hρΨ := ggLieF4Plane_image_eq hH i
  rcases ggLieF4Plane_shape hH i with hs | hs | hs
  · rcases ggLieF4Plane_recogA1 hH hf hqf i hs hρΨ with hS | hX
    · exact hsolv hS
    · rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.tuple_of_card_20160 hO
        hX.admissible hX hc with ⟨-, ⟨h3, -⟩ | ⟨h4, -⟩⟩ <;> omega
  · by_cases hin : twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u)
    · rcases ggLieF4Plane_recogA2in hH hf hqf i hs hρΨ hin with hS | hX
      · exact hsolv hS
      · rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.tuple_of_card_20160 hO
          hX.admissible hX hc with ⟨-, ⟨-, -, h2⟩ | ⟨h4, -⟩⟩
        · rw [h2] at hX
          exact CFSG.SeitzReduction.LinearPilot.not_lieModel_PSL_three_four hX hA3
        · omega
    · rcases ggLieF4Plane_recogA2out hH hf hqf i hs hρΨ hin with hS | hX
      · exact hsolv hS
      · have := CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.tuple_of_card_20160 hO
          hX.admissible hX hc
        exact absurd this.1 (by decide)
  · rcases ggLieF4Plane_recogB2 hH hf hqf i hs hρΨ with ⟨-, hd⟩ | hX
    · exact absurd (hc.symm.trans hd) (by decide)
    · have := CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.tuple_of_card_20160 hO
        hX.admissible hX hc
      exact absurd this.1 (by decide)

end CFSG.StandardType.LieCore
