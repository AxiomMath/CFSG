module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedF4ClassDefs
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGLieCoreCent
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsThree
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsOrder
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsSeven

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.StandardType.LieCore

theorem ggA6F4ClassInput_holds :
    GGA6F4ClassInput := by
  unfold GGA6F4ClassInput
  intro K _ _ hK G _ _ e p hp hp2 x hx hx1 D J L hDel hDc hxD hJx hL hJL hJA hDJ hDL
  rcases ggA6F4_prime_cases hK e hp hp2 hDc with rfl | rfl | rfl
  · exact ⟨rfl, ggA6F4_three hK e x hx L hL⟩
  · exact (ggA6F4_not_five hK e hDel hDc hJA hDJ).elim
  · exact (ggA6F4_not_seven hK e hDel hDc hJA hDJ).elim

end CFSG.StandardType.A6Red
