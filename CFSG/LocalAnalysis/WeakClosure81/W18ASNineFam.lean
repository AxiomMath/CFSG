module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNinePSU
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthMinus
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem tail189TwoNoSection_of_lieOrderFormulas (hO : LieOrderFormulasInput) :
    Tail189TwoNoSection :=
  tail189TwoNoSection_of_families (fun T _ hT => hT.two_dvd_card hO)
    (fun Y _ _ _ h => noSocle185Factor_of_isSpGp hO h)
    (fun Y _ _ _ h => noSocle185Factor_of_isPSUGp hO h)
    (fun Y _ _ _ h => noSocle185Factor_of_isOrthGp hO h)
    (fun Y _ _ _ h => noSocle185Factor_of_isL2WrSymGp hO h)
    (fun Y _ _ h => noSocle185Factor_of_isSymGp hO h)
    (fun Y _ h => noSocle185Factor_of_isOrth6MinusMod hO h)

section Reduction

variable {G : Type} [Group G] [Finite G]


theorem tail189Two_AS_of_lieOrderFormulas (hO : LieOrderFormulasInput)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (h772 : ∀ (X : Type) [Group X] [Finite X], SevenSevenTwoInput X)
    (hIn : OrthReflParabolic) : Tail189Two_AS G :=
  tail189Two_AS_of_inputs hCore hList h772 hIn (tail189TwoNoSection_of_lieOrderFormulas hO)

end Reduction

end CFSG.LocalAnalysis.WeakClosure81

end
