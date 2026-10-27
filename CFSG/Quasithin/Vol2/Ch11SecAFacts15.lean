module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def FactRankTwoLieSp4G2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    IsRankTwoLie2Derived (↥(StatedSp 2 K) ⧸ Subgroup.center ↥(StatedSp 2 K)) ∧
      IsRankTwoLie2Derived (↥⁅quasithinG2 K, quasithinG2 K⁆ ⧸
        Subgroup.center ↥⁅quasithinG2 K, quasithinG2 K⁆)

@[expose] def FactSylowLeviSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → P ≤ perfectCore (H ⊓ stabW U)

@[expose] def FactSylowLeviSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → P ≤ perfectCore (H ⊓ stabW U)

@[expose] def FactSylowLeviG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → P ≤ perfectCore (H ⊓ stabW U)

@[expose] def FactPointCentralizerSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U →
        ∀ h ∈ H, (∀ u ∈ U, h u * u⁻¹ ∈ Z) → h ∈ perfectCore (H ⊓ stabW U)

end CFSG.Quasithin.Vol2.Ch11.SecA
