module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldFixNsRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧
    (((lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .D ∧ 4 ≤ lab.rank ∧ ¬ (lab.rank = 4 ∧ p = 3) ∧ 2 ≤ lab.n) ∨
      (lab.tag = .twD ∧ 5 ≤ lab.rank ∧ 2 ≤ lab.n))

@[expose] def GGFieldFixNsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldFixNsRowLabel p lab ∧ GGFieldFixNsRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

end CFSG.StandardType

end
