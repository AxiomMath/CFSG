module

public import Certificates.Kernel.F4Inv.Final

@[expose] public section

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.LieType.Chevalley
  CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.LieType.Chevalley
  CFSG.ComponentClassification.RankTwoExceptional.F4Sec8 in
theorem certificate799601 :     Nat.card (Subgroup.centralizer ({tE} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7 ∧
      (∀ k : Fin 12, IsConj tE (f4Rep (ZMod 2) [f4PairLong k])) ∧
      (∀ x : F42C, orderOf x = 2 →
        Nat.card (Subgroup.centralizer ({x} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
          IsConj tE x ∨ IsConj uE x) ∧
      (¬IsConj rAE rBE ∧ ¬IsConj rAE zE ∧ ¬IsConj rBE zE) :=
  CFSG.KC.F4Inv.inv_facts_F42

end Certificates
