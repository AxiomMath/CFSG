module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL48TBForm1 : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGD4Three p lab →
        ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I

@[expose] def GGL48TBForm2 : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableBRk p R I (GGL48TB0Rank lab)

@[expose] def GGL48TBForm4 : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I

@[expose] def GGL48TBForm5 : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableBRk p R I (GGL48TB0Rank lab)

@[expose] def GGL48IrredOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twE6 ∧ 5 ≤ p) ∨ (lab.tag = .A ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1)

@[expose] def GGL48TableBKnownFormsRestRkOpen : Prop :=
  GGL48TBForm1 ∧ GGL48TBForm2 ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab
      → LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGD4Three p lab → LargeEvenLabelAll lab
      fun R _ I _ => GGIrredTableB p R I) ∧ GGL48TBForm4 ∧ GGL48TBForm5 ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → ¬
        GGL48TableBVacLabel p lab → ¬ GGD4Three p lab → ¬ GGL48F4TwoThreeLabel p lab → ¬
        GGL48TB0TwRow p lab → GGL48IrredOpenLabel p lab → LargeEvenLabelAll lab fun R _ I _ =>
        GGIrredModTableB p R I ∨ GGWPlusTableB p R I) ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
        LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRow p lab → LargeEvenLabelAll
        lab fun R _ I _ => GGIrredModTableBRk p R I (GGL48TB0Rank lab) ∨ GGWPlusTableBRk p R I
        (GGL48TB0Rank lab))

end CFSG.StandardType
