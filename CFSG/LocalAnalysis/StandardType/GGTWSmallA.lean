module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallARow
public import CFSG.LocalAnalysis.StandardType.GGTWSmallAL
public import CFSG.LocalAnalysis.StandardType.GGTWSmallAK
public import CFSG.LocalAnalysis.StandardType.GGTWHLCover
public import CFSG.LocalAnalysis.StandardType.GGTWKGuard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwoNodeDepSmallAInput_of_inputs
    (hRig : GGLabelRigidInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ : GGTBJInputR) (hJ2S : GGTBJTwoNodeSmallInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input)
    (hLE3 : GGResTwoNodeLE3SmallInput) (hIndep : GGResTwoNodeIndepInput)
    (hC : GGTWSmallCells) (hPZ : GGPZInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hMult : GGTWMultLeaves) (hZ : GGTWZKInput)
    (hHK : GGHL58NbrRestInput) (hHL : GGHL58BaseRestInput) : GGResTwoNodeDepSmallAInput := by
  have hT4 : GGTBTorAFrom 4 := ggTBTorAFrom_of_all (le_refl 4) hT
  have hLift4 : GGTBTorLiftAFrom 4 := ggTBTorLiftAFrom_of_rows (le_refl 4) hLift
  have hHK' : GGTWHKSmall :=
    ggTWHKSmall_of_rest hRig hT hLift hW hTw (ggTWHKGuard_holds hFix hFixK) hHK
  have hHL' : GGTWHLSmall := ggTWHLSmall_of_rest hRig hT hLift hW hTw hHL
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrowL, hxL⟩ | ⟨hrowK, hyK⟩
  · exact ggTWSmallA_L hRig hT4 hLift4 hW hR hTw hJ hJ2S hX h6c h6d h6e h6f h6g hLE3 hIndep hC
      hPZ hFix hFixK hMult hZ hHK' hH hF hS hE hrowL hxL
  · exact ggTWSmallA_K hRig hT4 hLift4 hW hR hTw hJ hJ2S hX h6c h6d h6e h6f h6g hLE3 hIndep hC
      hPZ hFix hFixK hMult hZ hHL' hH hF hS hE hrowK hyK
      (fun hrowL hxL => ggTWSmallA_L hRig hT4 hLift4 hW hR hTw hJ hJ2S hX h6c h6d h6e h6f h6g
        hLE3 hIndep hC hPZ hFix hFixK hMult hZ hHK' hH hF hS hE
        (ggTWSmallA_row_small_of_row hRig hrowK hrowL) hxL)

end CFSG.StandardType

end
