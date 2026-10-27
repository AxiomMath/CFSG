module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactB42SL3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (U Z : Subgroup V),
      Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
      B42ModulePair H U Z → BinaryNaturalSL H U Z 3 n

@[expose] def FactB42Sp4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (U Z : Subgroup V),
      Nonempty (↥H ≃* ↥(StatedSp 2 F)) →
      B42ModulePair H U Z → BinaryNaturalSp4 H U Z n

@[expose] def FactB42G2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (U Z : Subgroup V),
      Nonempty (↥H ≃* ↥⁅quasithinG2 F, quasithinG2 F⁆) →
      B42ModulePair H U Z → G2Natural H U Z n

@[expose] def KindModuleFacts : Prop :=
  FactB42SL3 ∧ FactB42Sp4 ∧ FactB42G2 ∧ SecA.FactG2DerivedOrder

end CFSG.Quasithin.Vol2.Ch11.SecC
