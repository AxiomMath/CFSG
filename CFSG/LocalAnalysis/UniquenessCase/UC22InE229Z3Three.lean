module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ResQ
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Thin
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3SU3
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem r847ResQ_of_three (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hThin : PartTwo.ThinList13) (hOut : RankThreeTheoremC.KFactOutCyclic) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hgr : GriessAllModelsStatement)
    (hC : uc22pwCartanSU3) (hres : L34GFResidueAt hS hU S) :
    (∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig, p = 3) → R847ResQ (UC6.dataOfSetup4 hS hU S) := by
  intro hall Y hY X hXY q hq hq5 hXc hcase
  obtain ⟨p, hp⟩ := (UC6S846.sigmaStd_dataOfSetup4 hS hU S).nonempty
  have hp3 : p = 3 := hall p hp
  subst hp3
  rcases hcase with hthin | ⟨n, hYn, hqn⟩
  · exact uc22ine229_normalizer_le_of_thin_three_setup4 hG3 hRee hK3 hThin hOut hS hU S hres hp hY
      hthin hq hq5 hXY hXc
  · exact uc22ine229_normalizer_le_of_isSU3_three_setup4 hG3 hRee hK3 hS hU S hgr hC hres hp hY
      hYn hq hq5 hqn hXY hXc

end CFSG.LocalAnalysis.UniquenessCase.UC22
