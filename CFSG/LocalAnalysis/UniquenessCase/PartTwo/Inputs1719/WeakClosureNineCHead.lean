module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCHeadC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCKill
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC7Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.WeakClosure81

theorem tcReduction_holds : TCReduction :=
  tcReduction_of_lemmas orbitStmt_holds killStmt_holds

theorem w3Lem914_holds_of (h7 : TCCoord7) (h9 : TCCoord9) (hM : TCCoordM10) (hA : TCCoordAut)
    (h3 : TCCoord3) (G : Type) [Group G] [Finite G] : W3Lem914 G :=
  w3Lem914_of_C (tcReduction_holds (tcCoord_of h7 h9 hM hA h3)) G

theorem w3Lem914_holds_of_coords (h9 : TCCoord9) (hM : TCCoordM10) (hA : TCCoordAut)
    (h3 : TCCoord3) (G : Type) [Group G] [Finite G] : W3Lem914 G :=
  w3Lem914_holds_of tcCoord7_holds h9 hM hA h3 G

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
