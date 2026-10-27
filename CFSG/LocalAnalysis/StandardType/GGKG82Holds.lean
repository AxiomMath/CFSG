module

public import CFSG.LocalAnalysis.StandardType.GGKG82TwoLocal
public import CFSG.LocalAnalysis.StandardType.GGKG82Inndiag
public import CFSG.LocalAnalysis.StandardType.GGKG82FieldRankFive
public import CFSG.LocalAnalysis.StandardType.GGNbrKGTwE6ThreeAtDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

namespace KG82

theorem ggTwoLocalAt_recipe
    {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) (hs : IsSimpleGroup (TwE6Delta.RecipeR K n))
    (hna : ∃ a b : TwE6Delta.RecipeR K n, a * b ≠ b * a)
    (hconj : GGRawFieldConj 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) (RecipeF K n)) :
    GGTwoLocalAt 3 5 6 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) (RecipeF K n) :=
  ggTwoLocalAt_recipe_of hn hK (exists_inndiag_rankFive hn hK h3)
    (fun _ hf hf3 => exists_inn_rankFive_fieldFixed hn hK h3 hf hf3) hs hna hconj

end KG82

theorem ggNbrKGTwE6ThreeAddTwoLocalAt_holds :
    GGNbrKGTwE6ThreeAddTwoLocalAt :=
  KG82.ggNbrKGTwE6ThreeAddTwoLocalAt_of_recipe
    (fun _ hn h3 _ _ _ hK hs hna hc => KG82.ggTwoLocalAt_recipe hn hK h3 hs hna hc)
    ggRawFieldConjInputExc_holds

end CFSG.StandardType
