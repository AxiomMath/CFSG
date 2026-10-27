module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJNaWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTBRowR1A (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 3 ≤ lab.rank

@[expose] def GGTBRowR1D (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D

@[expose] def GGTBRowR1E6 (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6

@[expose] def GGTBRowR1E7 (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E7

@[expose] def GGTBRowR1E8 (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E8

@[expose] def GGTBRowR1 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTBRowR1A p lab ∨ GGTBRowR1D p lab ∨ GGTBRowR1E6 p lab ∨ GGTBRowR1E7 p lab ∨
    GGTBRowR1E8 p lab

@[expose] def GGTBRowR2 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p = 3

@[expose] def GGTBDatumRowTarget (R : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ R p lab

@[expose] def GGTBJRowTarget (R : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ R p lab

@[expose] def GGTBJNoncommRowTarget (R : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGTBJNoncommReflOn fun p lab => GGLabQFour p lab ∧ R p lab

theorem ggTBJNoncommRowTarget_of_rowTarget {R : ℕ → LargeEvenLabel → Prop}
    (h : GGTBJRowTarget R) : GGTBJNoncommRowTarget R :=
  ggTBJNoncommReflOn_of_naWeyl h

end CFSG.StandardType

end
