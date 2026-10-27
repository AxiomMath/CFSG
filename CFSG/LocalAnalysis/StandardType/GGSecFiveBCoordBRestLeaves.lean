module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRestLeafDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFiveSplitDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniLeaves
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffSpSpQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinDense
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffSpSpPieces
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFour
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourCommon
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinFour
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinRec
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinSparse
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Split


theorem ggSecFiveBCoordBSparseTwDFive_of_split_nonsplit
    (hs : GGSecFiveBCoordBSparseOn fun n p lab =>
      5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1)
    (hns : GGSecFiveBCoordBSparseOn fun n p lab =>
      5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1) :
    GGSecFiveBCoordBSparseOn fun n _ lab => 5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hSpC hSpSpC hOmC hD
  have hLab' : GGInnerDiagOnLabel (fun p lab =>
      (GGSecFiveBCoordBLabel n p lab ∧
          (5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1)) ∨
        (GGSecFiveBCoordBLabel n p lab ∧
          (5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1))) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hPl => ⟨?_, hPl.2⟩) hLab
    obtain ⟨⟨hl, h5, h1, ht⟩, -⟩ := hPl
    have hl' := hl
    rcases hl' with ⟨ht' | ht', -⟩ | ⟨-, -, hd | ⟨-, hd⟩⟩ | ⟨ht', -⟩ | ⟨ht', -⟩
    · rw [ht] at ht'; cases ht'
    · rw [ht] at ht'; cases ht'
    · exact Or.inl ⟨hl, h5, h1, ht, hd⟩
    · exact Or.inr ⟨hl, h5, h1, ht, hd⟩
    · rw [ht] at ht'; cases ht'
    · rw [ht] at ht'; cases ht'
  rcases hLab'.elim_or with h | h
  · exact hs G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hSpC hSpSpC hOmC hD
  · exact hns G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hSpC hSpSpC hOmC hD

end Split

section Leaves


theorem ggSecFiveBCoordBOffSpSpInput_of_leaves (hO : GGSecFiveBCoordBOffQTwoOrthRouteInput)
    (hU4 : GGSecFiveBCoordBUniFourInput) (hU5 : GGSecFiveBCoordBUniLargeInput)
    (hCh : GGSecFiveBCoordBSpFourCommonChartRouteInput)
    (hCo : GGSecFiveBCoordBSpFourCommonCompRouteInput)
    (h4s : GGSecFiveBCoordBSparseTwDFourSplitInput)
    (h4n : GGSecFiveBCoordBSparseTwDFourNonsplitInput)
    (h5s : GGSecFiveBCoordBSparseTwDFiveSplitInput)
    (h5n : GGSecFiveBCoordBSparseTwDFiveNonsplitInput)
    (hK : GGSecFiveBCoordBDenseNbrLabelInput) (hKA : GGSecFiveBCoordBDenseNbrLinQTwoLabelInput)
    (hMp : GGInnerDiagMpInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hJ : BMaxJoinInput)
    (hLJ : GGSecFivePermNbrLabelOfJInput) (hU62 : GGU62OuterDiagInput) :
    GGSecFiveBCoordBOffSpSpInput := by
  have hfr := ggSecFiveBSpCoordFrameInput_of_mp hMp
  exact ggSecFiveBCoordBOffSpSpInput_of_orth_lin_large
    (hO hMp hLB hP hX hTCJ hRig hTPn hA8 hraw hiso hFC hJ hLJ hU62)
    (ggSecFiveBCoordBOffQTwoLinInput_of_rest (ggSecFiveBCoordBSparseEndpointOn_holds _)
      hX hTCJ hRig hTPn hA8 hraw hiso hFC
      (ggSecFiveBCoordBOffQTwoLinRestInput_of_rec hJ hKA
        (ggSecFiveBCoordBLinQTwoRecInput_of_lBalance hLB hP)
        (ggSecFiveBCoordBOffQTwoLinFourInput_of_inputs hX hTCJ hRig hTPn hA8 hraw hiso hFC)))
    (ggSecFiveBCoordBOffSpSpLargeInput_of_label hK
      (ggSecFiveBCoordBUniInput_of_leaves hMp hRig hU4 hU5) hJ
      (ggSecFiveBCoordBSparseLargeInput_of_sp_twD
        (ggSecFiveBCoordBSparseSpLargeInput_of_spFour
          (ggSecFiveBCoordBSpFourInput_of_cross hfr hRig
            (ggSecFiveBCoordBSpFourCrossInput_of_common hfr hRig
              (hCh hMp hLB hP hX hTCJ hRig hTPn hA8 hraw hiso hFC hJ)
              (hCo hMp hLB hP hX hTCJ hRig hTPn hA8 hraw hiso hFC hJ)) hJ)
          hX hTCJ hRig hTPn hA8 hraw hiso hFC)
        (ggSecFiveBCoordBSparseTwDLargeInput_of_four_five
          (ggSecFiveBCoordBSparseTwDFour_of_split_nonsplit h4s h4n hX hTCJ hRig hTPn hA8 hraw hiso
            hFC hJ)
          (ggSecFiveBCoordBSparseTwDFive_of_split_nonsplit
            (h5s hX hTCJ hRig hTPn hA8 hraw hiso hFC hJ)
            (h5n hMp hLB hP hX hTCJ hRig hTPn hA8 hraw hiso hFC hJ)))))

end Leaves

end CFSG.StandardType

end
