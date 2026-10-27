module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylIrredLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitFive
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGStdSubExistDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExc
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylField
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylProvedLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrNsVacLabel p lab ∨ GGNbrWeylFieldVacA2Label p lab ∨ GGNbrWeylInnerIrredLabel p lab ∨
    GGNbrWeylInnerTypeALabel p lab ∨ GGNbrWeylUnitDvdLabel p lab ∨ GGNbrWeylUnitThreeLabel p lab ∨
    GGNbrWeylUnitFiveLabel p lab ∨ GGNbrWeylInnerExcProvedLabel p lab

theorem ggNbrWeylRest12Label_cover_rest13 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (hR : GGNbrWeylRest12Label p lab) :
    GGNbrWeylProvedLabel p lab ∨ GGNbrWeylRest13Label p lab := by
  rcases ggNbrWeylRest12Label_cover p lab hR with h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · rcases ggNbrWeylFieldLabel_cases h with h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr ⟨hR, Or.inl h⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr ⟨hR, Or.inr (Or.inl h)⟩
  · rcases ggNbrWeylInnerExcLabel_cases_open hp hp2 hlab h with h | h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · exact Or.inr ⟨hR, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inr ⟨hR, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact Or.inr ⟨hR, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩

section Exact

attribute [local simp] GGNbrWeylProvedLabel GGNbrNsVacLabel GGNbrNsSpLabel GGNbrNsOrthLabel
  GGNbrNsLinLabel GGNbrNsUnitLabel GGNbrNsE7Label GGNbrNsE6Label GGNbrNsTwE6Label GGNbrNsF4Label
  GGNbrNsE8Label GGNbrNsTriD4Label GGNbrNsTwF4Label GGNbrWeylFieldVacA2Label
  GGNbrWeylInnerIrredLabel GGReflSpLabel GGSpNonsplitLabel GGCorFourTwoOrthSplitLabel
  GGOrthNsLabel GGTableBNbrInnerExcSplitLabel GGTableBF4Label GGUnitaryCoprimeLabel
  GGNbrWeylInnerTypeALabel GGTableBNbrInnerTypeADvdLabel GGNbrWeylUnitDvdLabel
  GGNbrWeylUnitThreeLabel GGNbrWeylUnitFiveLabel GGNbrWeylInnerExcProvedLabel
  GGNbrWeylE6TwoLabel GGNbrWeylTwE6SplitLabel GGNbrWeylExcPlusLargePrimeLabel
  GGNbrWeylExcPlusLabel GGNbrWeylTwF4Label GGNbrWeylUnitSixThreeLabel
  GGNbrWeylE6ThreeDvdLabel GGNbrWeylTwE6RestLabel GGNbrWeylExcPlusSmallPrimeLabel

end Exact

section Main

theorem ggNbrInnerWeylOn_proved : GGNbrInnerWeylOn GGNbrWeylProvedLabel :=
  ggNbrInnerWeylOn_nsVac.or (ggNbrInnerWeylOn_fieldVacA2.or (ggNbrInnerWeylOn_innerIrred.or
    (ggNbrInnerWeylOn_innerTypeA.or (ggNbrInnerWeylOn_unitDvd.or (ggNbrInnerWeylOn_unitThree.or
    (ggNbrInnerWeylOn_unitFive.or ggNbrInnerWeylOn_innerExcProved))))))

theorem ggNbrInnerWeylOn_rest12_of_rest13 (h : GGNbrInnerWeylOn GGNbrWeylRest13Label) :
    GGNbrInnerWeylOn GGNbrWeylRest12Label :=
  (ggNbrInnerWeylOn_proved.or h).mono_of_lambda fun _ _ hp hp2 hlab hR =>
    ggNbrWeylRest12Label_cover_rest13 hp hp2 hlab hR

end Main

end CFSG.StandardType

end
