module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08SmallCells
public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Cell
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellsFull
public import CFSG.LocalAnalysis.StandardType.GGQ2S08E7Full

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_cell_twA5a
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) :
    GGQ2S08Cell .twA 5 .a := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  exact ggQ2s08a6_refl hLB hP hRig hΓi hS hI1 hCav M hShape hMark ⟨htag, hrank, hq⟩ hWeyl hTBN g φ
    hInd hRefl

theorem ggQ2s08_cell_E7 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .E7 0 .full :=
  ggQ2s08_cellE7_of_test hLB hP hΓi hTBN fun A Mg hT r hr hrR hrx t ht htR htx =>
    TestLin.e7full_test A Mg hT r hr hrR hrx t ht htR htx

end CFSG.StandardType

end
