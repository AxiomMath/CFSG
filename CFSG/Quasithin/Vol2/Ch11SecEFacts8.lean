module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def List11_1_1List701Fact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n →
    (List11_1_1Two X n ∨ (n = 2 ∧ List11_1_1Three X)) → ¬ A36Case4 X → ¬ IsSL2pE X →
    ∀ (Y : Type) [Group Y] (π : X →* Y), Function.Surjective π →
      π.ker ≤ Subgroup.center X → List701Excl Y →
      (IsSL3 (2 ^ n) X ∨ IsPSL 3 2 n X ∨ IsPSp4 2 n X ∨ IsG2 2 n X) ∨
        (n = 2 ∧ (IsAlt 7 X ∨ IsHat X (alternatingGroup (Fin 7))))

@[expose] def List11_1_1ThreeQuasisimpleFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], List11_1_1Three X → ¬ A36Case4 X → ¬ IsSL2pE X →
    CFSG.IsQuasisimple X

structure Facts42S3 : Prop where
  list701 : List11_1_1List701Fact
  threeQS : List11_1_1ThreeQuasisimpleFact

end CFSG.Quasithin.Vol2.Ch11.SecE
