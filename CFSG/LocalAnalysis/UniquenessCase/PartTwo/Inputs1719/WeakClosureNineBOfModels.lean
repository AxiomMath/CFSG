module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBRed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBIdent
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeDischarge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.WeakClosure81


theorem w3Lem915_of_modelFacts (hM : NGM.NGModelFacts) (G : Type) [Group G] [Finite G] :
    W3Lem915 G :=
  nGReduction_holds (fun _ _ _ V => sevenSixThreeAbelian_holds V) ngAbstract_holds
    (NGM.nGFactsOfModel_holds NGM.nGIdent_holds hM) G

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
