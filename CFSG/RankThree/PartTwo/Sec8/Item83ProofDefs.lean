module

public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Certs

@[expose] def Item82Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → 27 < Nat.card A →
      Nat.card A = 81 ∧ IsList82Two (L ⧸ aschbacherSolvableCore 3 L)

@[expose] def KF83GTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Odd n → Nat.card K = 2 ^ (3 * n) →
    ∀ σ : K ≃+* K, orderOf σ = 3 →
      ∃ y₁ y₂ : adjointGroup Tag.G2 (fixSubfield σ), y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧
        y₁ * y₂ = y₂ * y₁ ∧ y₁ ≠ 1 ∧ y₂ ∉ Subgroup.zpowers y₁ ∧
        Nonempty (inSubgroup perfectResidual
            (Subgroup.centralizer ({KFacts.g2Incl σ y₁} : Set (adjointGroup Tag.G2 K))) ≃*
          projSL 2 (GaloisField 2 (3 * n)))

@[expose] def KF83TrialityD4 : Prop :=
  ∀ n : ℕ, Odd n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (hK2 : ringChar K = 2),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ z : adjointGroup Tag.G2 (fixSubfield σ), z ^ 3 = 1 →
      ∃ y₁ y₂ : adjointGroup Tag.G2 (fixSubfield σ), y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧
        y₁ * y₂ = y₂ * y₁ ∧ y₁ ≠ 1 ∧ y₂ ∉ Subgroup.zpowers y₁ ∧
        z ∈ Subgroup.closure ({y₁, y₂} : Set (adjointGroup Tag.G2 (fixSubfield σ))) ∧
        Nonempty (inSubgroup perfectResidual
            (Subgroup.centralizer ({KFacts.trialityG2Incl σ hK2 y₁} :
              Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
          projSL 2 (GaloisField 2 (3 * n)))

@[expose] def KF83ReeF4 : Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (n : ℕ),
    1 ≤ a → 2 * a + 1 = 3 * n → Nat.card K = 2 ^ (2 * a + 1) →
    ∀ β : K ≃+* K, orderOf β = 3 →
      IsoReeF4 (Sec4.autFix (ReeTag.F4.reeGammaFieldAut K a β)) n ∧
      ∃ y₁ y₂ : ReeTag.F4.reeGamma K a, ReeTag.F4.reeGammaFieldAut K a β y₁ = y₁ ∧
        ReeTag.F4.reeGammaFieldAut K a β y₂ = y₂ ∧ y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧
        y₁ * y₂ = y₂ * y₁ ∧ y₁ ≠ 1 ∧ y₂ ∉ Subgroup.zpowers y₁ ∧
        IsoSUThree (inSubgroup perfectResidual
          (Subgroup.centralizer ({y₁} : Set (ReeTag.F4.reeGamma K a)))) (2 ^ (3 * n))

end Certs

@[expose] def KF83SUThree : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Odd n → Nat.card K = (2 ^ (3 * n)) ^ 2 →
    ∀ g : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * n)) K,
      g ^ 3 ∈ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * n)) K) →
      g ^ 3 ≠ 1 →
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
          ({g} : Set (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * n)) K))) ≃*
        projSL 2 (GaloisField 2 (3 * n)))

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
