module

public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree.PartTwo

@[expose] def KS17J2NotList : Prop :=
  (∀ (p e : ℕ) [Fact p.Prime], ¬ Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.J2 p e) ∧
    IsEmpty (CFSG.Blueprint.NativeSporadic.J2 ≃* alternatingGroup (Fin 7)) ∧
    IsEmpty (CFSG.Blueprint.NativeSporadic.J2 ≃* CFSG.Blueprint.NativeSporadic.M22)

end CFSG.RankThree.PartTwo.KFacts
