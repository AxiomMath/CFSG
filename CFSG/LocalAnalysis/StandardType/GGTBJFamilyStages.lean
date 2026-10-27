module

public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggTBJEThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ p ∣ 4 ^ lab.n - 1 ∧ ¬ (p = 7 ∧ (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩)) ∧
    ¬ (lab.tag = .twD ∧ lab.rank = 2) ∧ ¬ (lab.tag = .A ∧ lab.rank = 1)

@[expose] def ggTBJSevenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 7 ∧ (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.A, 11, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩ ∨
    lab = ⟨.E8, 0, 1⟩)

@[expose] def GGTBJOrderRestSplitAUnitSevenInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab

@[expose] def ggTBJSpPlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTBJOrderRestSplitAUnitSpPlusInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab

@[expose] def ggTBJLinMinusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGTBJOrderRestSplitAUnitSpPlusEThreeLinMinusInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab

@[expose] def ggTBJUniMinusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTBJOrderRestSplitAUnitSpPlusEThreeLinMinusUniMinusInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab

@[expose] def ggTBJSympMinusGeTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n

@[expose] def GGTBJOrderRestSplitAUnitSpPlusEThreeLinMinusUniMinusSympMinusGeTwoInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab

@[expose] def ggTBJOrthLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  1 ≤ lab.n ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧
    (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)

@[expose] def GGTBJOrderRestSplitAUnitSpPlusEThreeLinMinusUniMinusSympMinusGeTwoOrthInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab

@[expose] def ggTBJSympMinusOneLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ lab.n = 1

@[expose] def GGTBJOrderRestSplitAUnitSpPlusEThreeLinMinusUniMinusSympMinusGeTwoOrthSympMinusOneInput :
    Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab

@[expose] def GGTBJOrderRestUnitaryCoprimeInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)

@[expose] def ggTBJF4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ GGLabPhiOneTwo p lab

@[expose] def ggTBJF4LabelNeTwoThree (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggTBJF4Label p lab ∧ ¬ (p = 3 ∧ lab.n = 1)

@[expose] def GGTBJOrderRestUnitaryCoprimeF4Input : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab

@[expose] def GGTBJOrderRestSplitAUnitSpRankThreeInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab) ∨ ggTBJSpRankThreeLabel p lab

@[expose] def ggTBJTwE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ GGLabPhiOneTwo p lab

@[expose] def ggTBJTwE6LabelGeFive (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggTBJTwE6Label p lab ∧ 5 ≤ p ∧ ¬ 3 ∣ 2 ^ lab.n + 1 ∧ ¬ (5 < p ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGTBJOrderRestSplitAUnitSpRankThreeTwE6GeFiveInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab) ∨ ggTBJSpRankThreeLabel p lab) ∨ ggTBJTwE6LabelGeFive p lab

@[expose] def ggTBJTwE6LabelFoldCover (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggTBJTwE6Label p lab ∧ 5 < p ∧ 3 ∣ 2 ^ lab.n + 1 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTBJOrderRestSplitAUnitSpRankThreeTwE6GeFiveFoldCoverInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab) ∨ ggTBJSpRankThreeLabel p lab) ∨ ggTBJTwE6LabelGeFive p lab) ∨ ggTBJTwE6LabelFoldCover p lab

@[expose] def ggTBJE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ GGLabPhiOneTwo p lab

@[expose] def GGTBJOrderRestSplitAUnitSpRankThreeTwE6GeFiveFoldCoverE6Input : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab) ∨ ggTBJSpRankThreeLabel p lab) ∨ ggTBJTwE6LabelGeFive p lab) ∨ ggTBJTwE6LabelFoldCover p lab) ∨ ggTBJE6Label p lab

@[expose] def GGTBJOrderRestSplitAUnitSpRankThreeTwE6GeFiveFoldCoverE6F4Input : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    ((((((((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab) ∨ ggTBJSpRankThreeLabel p lab) ∨ ggTBJTwE6LabelGeFive p lab) ∨ ggTBJTwE6LabelFoldCover p lab) ∨ ggTBJE6Label p lab) ∨ ggTBJF4Label p lab

@[expose] def ggTBJTwE6LabelThree (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggTBJTwE6Label p lab ∧ p = 3

@[expose] def GGTBJOrderRestSplitAUnitSpRankThreeTwE6GeFiveFoldCoverE6F4TwE6ThreeInput : Prop :=
  GGTBJOrdinaryOutside fun p lab =>
    (((((((((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
        ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
          ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
            ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨ ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨ (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab) ∨ ggTBJSpRankThreeLabel p lab) ∨ ggTBJTwE6LabelGeFive p lab) ∨ ggTBJTwE6LabelFoldCover p lab) ∨ ggTBJE6Label p lab) ∨ ggTBJF4Label p lab) ∨ ggTBJTwE6LabelThree p lab

end CFSG.StandardType

end
