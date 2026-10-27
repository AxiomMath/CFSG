module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)

@[expose] def KF148PGUFieldCent : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 2 ^ f % 9 = 8 →
    ∀ σ : K ≃+* K, orderOf σ = 3 → ∀ A : unitaryIsom3 h, glAut σ (A : GL (Fin 3) K) = A →
      ∃ g : unitarySU 2 f K 3, psuConj h A = MulAut.conj (unitaryProj h 3 g) ∧
        psuField h σ (unitaryProj h 3 g) = unitaryProj h 3 g

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
