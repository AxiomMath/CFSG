module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCHead
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoord9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordM10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.WeakClosure81

theorem w3Lem914C_holds (G : Type) [Group G] [Finite G] : W3Lem914C G :=
  tcReduction_holds (tcCoord_of tcCoord7_holds tcCoord9_holds tcCoordM10_holds tcCoordAut_holds
    tcCoord3_holds) G

theorem w3Lem914N_of_C {G : Type} [Group G] [Finite G] (h : W3Lem914C G) : W3Lem914N G :=
  fun V T N L hyp hTN hNM hN hL _ hψ hφ hstar => h V T N L hyp hTN hNM hN hL hψ hφ hstar

theorem w3Lem914N_holds (G : Type) [Group G] [Finite G] : W3Lem914N G :=
  w3Lem914N_of_C (w3Lem914C_holds G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
