module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwF4
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylInnerExcProvedLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (GGNbrWeylE6TwoLabel p lab ∨ GGNbrWeylTwE6SplitLabel p lab) ∨
    (GGNbrWeylExcPlusLargePrimeLabel p lab ∨ GGNbrWeylTwF4Label p lab)

theorem ggNbrWeylInnerExcLabel_cases_open {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (h : GGNbrWeylInnerExcLabel p lab) :
    GGNbrWeylInnerExcProvedLabel p lab ∨ GGNbrWeylE6ThreeDvdLabel p lab ∨
      GGNbrWeylTwE6RestLabel p lab ∨ GGNbrWeylExcPlusSmallPrimeLabel p lab := by
  rcases ggNbrWeylInnerExcLabel_cases hp hp2 hlab h with h | h | h | h
  · rcases ggNbrWeylE6Label_cases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl h)
  · rcases ggNbrWeylTwE6Label_cases h with h | h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases ggNbrWeylExcPlusLabel_cases h with h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl (Or.inr (Or.inr h))

section Main

theorem ggNbrInnerWeylOn_innerExcProved : GGNbrInnerWeylOn GGNbrWeylInnerExcProvedLabel :=
  (ggNbrInnerWeylOn_e6Two.or ggNbrInnerWeylOn_twE6Split).or
    (ggNbrInnerWeylOn_excPlusLarge.or ggNbrInnerWeylOn_twF4)

end Main

end CFSG.StandardType

end
