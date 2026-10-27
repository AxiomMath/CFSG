module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def IsL2OrSz (X : Type) [Group X] (n : ℕ) : Prop :=
  CFSG.Quasithin.IsPSL 2 2 n X ∨ CFSG.Quasithin.IsSz n X

@[expose] def TwoConjugateGeneration : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 1 < n → IsL2OrSz S n →
    ∀ A : Subgroup S, CFSG.Open.IsElemAbelian 2 A → 2 < Nat.card A →
      ∃ g : S, A ⊔ CFSG.Quasithin.conjSubgroup A g = ⊤

end CFSG.LocalAnalysis.WeakClosure81.SevenK
