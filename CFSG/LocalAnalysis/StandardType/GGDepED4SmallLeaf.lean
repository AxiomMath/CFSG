module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LRead
public import CFSG.LocalAnalysis.StandardType.GGDepED4KRead
public import CFSG.LocalAnalysis.StandardType.GGDepED4RowSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwoNodeDepSmallEInput_of_inputs
    (hRig : GGLabelRigidInput) (hJ : GGTBJInputR)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input)
    (hLE3 : GGResTwoNodeLE3SmallInput) (hIndep : GGResTwoNodeIndepInput)
    (hLoc : GGE6D4TwoNodeLocalInput) (hZ : GGDepED4ZKInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) (hLow : GGDepED4LowClose)
    (hLowK : GGDepED4LowCloseK) (h58 : GGDepED4L58RowInput) : GGResTwoNodeDepSmallEInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrowL, hxL⟩ | ⟨hrowK, hyK⟩
  · exact ggDepED4_L hRig hJ hX h6c h6d h6e h6f h6g hLE3 hIndep hLoc hZ hFix hFixK hPZ hLow h58
      hH hF hS hE hrowL hxL
  · exact ggDepED4_K hRig hJ hX h6c h6d h6e h6f h6g hLE3 hIndep hLoc hFix hFixK hPZ hLowK h58
      hH hF hS hE hrowK hyK
      (fun hrowL hxL => ggDepED4_L hRig hJ hX h6c h6d h6e h6f h6g hLE3 hIndep hLoc hZ hFix hFixK
        hPZ hLow h58 hH hF hS hE (ggDepED4_row_small_of_row hRig hrowK hrowL) hxL)

end CFSG.StandardType

end
