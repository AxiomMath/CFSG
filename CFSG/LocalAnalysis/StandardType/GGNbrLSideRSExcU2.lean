module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU2TypeA
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU2NonA
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU2E6
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.LocalAnalysis.GLTheoremA.K155X

theorem ggNbrLSideRSExc_u2_of_excl
    (hExcl : GGNbrLSideRSExcExcl) : GGNbrLSideRSExcU2 := by
  intro τ L _ _ p₀ S h2 a i Q hP
  by_cases hA : L154TypeAClass a i
  · exact ggNbrLSideRSExc_u2_typeA hExcl S h2 hP hA
  · by_cases hE : L154E6Class a i
    · exact (ggNbrLSideRSExc_u2_e6 hExcl S h2 hP hE).elim
    · exact (ggNbrLSideRSExc_u2_nonA hExcl S h2 hP hA hE).elim

theorem ggNbrLSideRSExcU2_holds
    : GGNbrLSideRSExcU2 := by
  refine ggNbrLSideRSExc_u2_of_excl ?_
  intro X _ F _ _ hF4 e t m f hX
  exact ggNbrLSideExcl CFSG.LocalAnalysis.GLTheoremA.cls_det
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hF4 e hX

end CFSG.StandardType
