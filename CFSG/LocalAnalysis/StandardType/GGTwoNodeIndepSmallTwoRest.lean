module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepSmallTwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6Consumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6ShapeK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5Consumer
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallTwoSides

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwoNodeIndepSmallTwoThree_of_all
    (hAll : LR6E6All) (hAll5 : LR6A5All) (hOrb : GGResCentBoundInput)
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hKFix : GGTwoNodeKFixLineInput) (hD : GGTwoNodeIndepDatum) (hLoc : GGE6D4TwoNodeLocalInput)
    (hRig : GGLabelRigidInput) (hJ : GGTBJInputR) (hX : GGResXDichotomyInput)
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) : GGResTwoNodeIndepSmallTwoThreeInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  obtain ⟨hp3, hP⟩ := hP
  rcases hP with ⟨hrow, hxL⟩ | ⟨hrow, hyK⟩ | ⟨hrow, hxL, hnK⟩ | ⟨hrow, hyK, hnL⟩
  · exact ggResTwoNodeIndepE6L hAll hOrb hFix hFixK hLoc hH hrow hxL
  · exact ggResTwoNodeIndepE6K hAll hOrbK hFix hFixK hLoc hRig hJ hX h6c h6d h6e h6f h6g hH hF hS hE
      hrow hyK
  · exact ggResTwoNodeIndepA5L hAll5 hOrb hFix hFixK hD hp3 hH hrow hxL
  · exact ggResTwoNodeIndepA5K hAll5 hOrbK hFix hKFix hD hp3 hH hF hS hE hrow hyK hnL

theorem ggResTwoNodeIndepSmallTwo_of_three (hUse : ZS.UseInput) (hExcl : LR6SmallRankExcl)
    (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hKFix : GGTwoNodeKFixLineInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput)
    (hThree : GGResTwoNodeIndepSmallTwoThreeInput) : GGResTwoNodeIndepSmallTwoInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  by_cases hp3 : p = 3
  · exact hThree G p B Bs x L D J y K hH hF hS hE ⟨hp3, hP⟩
  rcases hP with ⟨hrow, hxL⟩ | ⟨hrow, hyK⟩ | ⟨hrow, hxL, hK⟩ | ⟨hrow, hyK, hL⟩
  · exact (hp3 hrow.smallE6_prime_three).elim
  · exact (hp3 hrow.smallE6_prime_three).elim
  · exact ggResTwoNodeIndepSmallTwoL_A hUse hExcl hOrb hFix hFixK hJr hPump hLB hSP
      hD hJ2 hp3 hH hrow hxL hK
  · exact ggResTwoNodeIndepSmallTwoK_A hUse hExcl hOrbK hFix hKFix hJr hPump hLB hSP
      hD hJ2 hp3 hH hF hS hE hrow hyK hL

end CFSG.StandardType

end
