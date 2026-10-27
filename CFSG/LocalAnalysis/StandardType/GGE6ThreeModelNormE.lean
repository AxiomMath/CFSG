module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiag

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

theorem eFrame_norm {ζ : Kˣ} (hζ : ζ ^ 3 = 1) : (eFrame K ζ hζ).NormOK := by
  intro r S _ hS
  have hh : (MulAut.conj r : MulAut (adjointGroup .E6 K)) ∈ (hatAut .E6 K).range :=
    ⟨⟨(r : ModGL .E6 K), adjointGroup_le_hatGroup r.2⟩, MulEquiv.ext fun h => Subtype.ext rfl⟩
  exact NoOffE6Three.exists_weyl_conj_diag3 (W := S) hζ hh hS

end CFSG.StandardType.E6ThreeModel
