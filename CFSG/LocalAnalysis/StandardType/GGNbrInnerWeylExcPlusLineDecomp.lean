module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusPrimes
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeE7
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeE8
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylExcPlusSmallPrimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylExcPlusLabel p lab ∧
    (((lab.tag = .E7 ∨ lab.tag = .E8) ∧ GGNbrExcPlusSmallPrimeE7E8 p) ∨
      (lab.tag = .F4 ∧ GGNbrExcPlusSmallPrimeF4 p))

@[expose] def GGNbrWeylExcPlusLargePrimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylExcPlusLabel p lab ∧ ¬ GGNbrWeylExcPlusSmallPrimeLabel p lab

theorem ggNbrWeylExcPlusLabel_cases {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrWeylExcPlusLabel p lab) :
    GGNbrWeylExcPlusLargePrimeLabel p lab ∨ GGNbrWeylExcPlusSmallPrimeLabel p lab := by
  by_cases hs : GGNbrWeylExcPlusSmallPrimeLabel p lab
  · exact Or.inr hs
  · exact Or.inl ⟨h, hs⟩

end CFSG.StandardType

end
