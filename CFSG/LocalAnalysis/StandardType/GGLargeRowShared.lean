module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLargeRowDimKnown_of_twoNode (h : GGTwoNodeRowDimKnown) : GGLargeRowDimKnown := by
  intro G _ _ p _ B Bs x L D J y K N hH hrow
  obtain ⟨labJ, labX, hΛJ, hΛX, hLabJ, hLabX, hRow2, hrankX, hN⟩ := hrow
  obtain ⟨-, hdvd, -⟩ := l05nAK_row_facts hRow2 hrankX
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hpN : p ∣ N := by rw [← hN]; exact hdvd
  exact h G p B Bs x L D J y K N hH
    ⟨labJ, labX, hΛJ, hΛX, hLabJ, hLabX, hRow2, hN⟩ hp2 (by omega) hpN

theorem ggLargeRowNoSevenAtL_of_tcj (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) :
    GGLargeRowNoSevenAtL := by
  intro G _ _ p _ B Bs x L D J y K N hH _ hL
  obtain ⟨labJ, labX, hΛJ, hΛX, hLabJ, hLabX, hp7, h5⟩ := hL
  obtain ⟨hcfg, -, -, -, hnb, -, -⟩ := hH
  exact ggSeven_L_absurd hTCJ hRig hcfg hp7 hnb hΛX hLabX (by simpa only [GGSevenLabel] using h5)

end CFSG.StandardType

end
