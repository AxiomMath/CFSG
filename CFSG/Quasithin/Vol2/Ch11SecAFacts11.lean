module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def FactPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U →
        ∀ h ∈ perfectCore (H ⊓ stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z

@[expose] def FactPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U →
        ∀ h ∈ perfectCore (H ⊓ stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z

@[expose] def FactPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U →
        ∀ h ∈ perfectCore (H ⊓ stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z

@[expose] def FactL2Parabolic : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L P : Subgroup Q) (m : ℕ), 2 ≤ m →
    IsRank2LieChar2 ↥L → IsMaxParabolic2 L P → IsPSL 2 2 m (ModO2 (perfectCore P)) →
      List11_1_1Two ↥L m

structure Facts11 : Prop where
  pointSL3 : FactPointSL3
  pointSp4 : FactPointSp4
  pointG2 : FactPointG2
  parab : FactL2Parabolic

end CFSG.Quasithin.Vol2.Ch11.SecA
