module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwoANarrow21Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOmegaPlusTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOmegaMinusTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TBDThreeRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGL48TBUFourRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGL48TBOrthRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)

@[expose] def GGL48TBForm4RestTwoThree : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGL48TB0TwRow p lab →
        ¬ GGL48TBTypeARow p lab → ¬ GGL48TBTwistedARow p lab → ¬ GGTableBSympLabel p lab →
        ¬ GGL48TBTwE6Row p lab → ¬ GGL48TBTwoARow p lab → ¬ GGSpTwoThreeLabel p lab →
        ¬ GGOmegaPlusTwoThreeLabel p lab → ¬ GGOmegaMinusTwoThreeLabel p lab →
        ¬ GGL48TBDThreeRow p lab → ¬ GGL48TBExcInnRow p lab → ¬ GGL48TBE6Row p lab →
        ¬ GGL48TBUFourRow p lab → ¬ GGL48TBExcTwoRow p lab → ¬ GGL48TBOrthRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I

@[expose] def GGL48TBForm1InnerRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ p ∣ lab.n ∧ (lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ 4 ≤ lab.rank) ∨
    (lab.tag = .twD ∧ 3 ≤ lab.rank) ∨ (lab.tag = .twA ∧ lab.rank = 3))

@[expose] def GGL48TBForm1Rest22 : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGD4Three p lab →
    ¬ GGL48TB0TwRow p lab → ¬ GGL48TBTypeARow p lab → ¬ GGL48TBTwoARow p lab →
    ¬ GGL48TBTwistedARow p lab → ¬ GGL48TBExcInnRow p lab → ¬ GGL48TBExcTwoRow p lab →
    ¬ GGL48TBE6Row p lab → ¬ GGL48TBTwE6Row p lab → ¬ GGL48TBDThreeRow p lab →
    ¬ GGL48TBForm1InnerRow p lab → ¬ GGTableBSympLabel p lab → ¬ GGL48TBUFourRow p lab →
    ¬ GGTableBOrthSplitLabel p lab →
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I

@[expose] def GGL48TableBKnownFormsRestRkOpen22 : Prop :=
  GGL48TBForm1Rest22 ∧ GGL48TBForm4RestTwoThree

end CFSG.StandardType
