module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBGlue
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIModel
public import CFSG.LocalAnalysis.StandardType.GGLieOddCover

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.Open

theorem rckRowK1_II_of_tri
    (hcov : LieOddCover.GGLieOddCover)
    (hTri : ∀ (F : Type) [Field F] [Finite F] (σ : F →+* F), TriField F σ 1 →
      RCKRowIIAtTri F σ) :
    RCKRowK1 .II RCKPosRootElt := by
  refine rckRowK1_II_of_at hcov ?_ hTri
  intro t n hM hadm
  rcases hM with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | rfl | rfl | rfl | rfl | rfl
  · exact rckRowIIAt_PSL n hn hadm
  · exact rckRowIIAt_OmegaPlus n hn hadm
  · exact rckRowIIAt_OmegaMinus n hn hadm
  · exact rckRowIIAt_E6 n hadm
  · exact rckRowIIAt_E7 n hadm
  · exact rckRowIIAt_E8 n hadm
  · exact rckRowIIAt_F4 n hadm
  · exact rckRowIIAt_TwE6 n hadm

end CFSG.StandardType.RCKK1II
