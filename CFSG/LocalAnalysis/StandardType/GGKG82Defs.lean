module

public import CFSG.LocalAnalysis.StandardType.GGNbrKGTwE6ThreeAtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.StandardType.KG82

open CFSG CFSG.Assembly CFSG.Blueprint

abbrev RecipeF (K : Type) [Field K] (n : ℕ) : Set (MulAut (TwE6Delta.RecipeR K n)) :=
  LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)

end CFSG.StandardType.KG82
