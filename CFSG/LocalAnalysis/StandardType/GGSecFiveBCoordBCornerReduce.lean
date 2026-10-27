module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerRowOneLevi
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerHyp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerJ
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggSecFiveBCoordBProperInput_of_rows (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    (hCP : GGLabelCenterPCyclicInput) (h : GGSecFiveBCoordBProperRowsInput) :
    GGSecFiveBCoordBProperInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hT1 n e hcox hn4 eta i0 hfull hb hM hne hNbr hG0
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hn5, -, -, hp⟩, -⟩ := largeEvenMarking_exists' hM
  subst hp
  have hM' : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧
      lab.rank = n - 1 ∧ lab.n = 1) 3 Bs L :=
    hM.mono_label fun _ hl => GGSecFiveBCoordBLabel.corner_tag_rank hl
  have hC : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨R, z, c, hD, hc, hJ, hrow⟩ :=
    hC.cornerRows hn5 eta hb hM' hne (hC.exists_corner_involution hn5 eta hb hM' hne)
  rcases hrow with ⟨k, -, -, rfl⟩ | hrest
  · exact (GGSecFiveRouteCfg.false_of_cornerRowOne hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB hCP
      hcfg e hcox eta hfull hb hM R hJ).elim
  · exact h G 3 B Bs x L D J 𝒦 hcfg hT1 n e hcox hn4 eta i0 hfull hb hM hne
      (ggSecFiveBCoordB_corner_hyperplane hC hn5 eta hb hM' hne) ⟨R, z, c, hD, hc, hJ, hrest⟩
      hNbr hG0

end CFSG.StandardType

end
