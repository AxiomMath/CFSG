module

public import CFSG.Open.Defs
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.Open
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] noncomputable def uniqueFourTwoLocalRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  twoLocalPrimeRank p G

@[expose] def uniqueFourBeta (G : Type*) [Group G] [Finite G] : Set ℕ :=
  {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 4 ≤ uniqueFourTwoLocalRank p G}

@[expose] def uniqueFourIsBmax [Finite G] (p : ℕ) (B : Subgroup G) : Prop :=
  IsElemAbelian p B ∧ Nat.card B = p ^ uniqueFourTwoLocalRank p G ∧
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)

@[expose] def uniqueFourSigma [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p ∈ uniqueFourBeta G ∧ ∃ B : Subgroup G, uniqueFourIsBmax p B ∧ B ≤ M}

@[expose] def uniqueFourIsMaxTwoLocal (M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M

@[expose] noncomputable def uniqueFourGamma [Finite G] (p : ℕ) (P : Subgroup G) : Subgroup G :=
  GLBCore p 2 P

@[expose] def uniqueFourPrimeCore (p : ℕ) (H : Subgroup G) : Subgroup G :=
  relPPrimeCore p H

@[expose] def uniqueFourLayer (H : Subgroup G) : Subgroup G :=
  sSup {L | IsComponentOf L H}

@[expose] def uniqueFourConj (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def uniqueFourIsFrobenius (R K V : Subgroup G) : Prop :=
  K ≠ ⊥ ∧ V ≠ ⊥ ∧ K ≤ R ∧ (K.subgroupOf R).Normal ∧ V ≤ R ∧ R = K ⊔ V ∧ K ⊓ V = ⊥ ∧
    ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1

@[expose] def uniqueFourClauseTwo [Finite G] (M P P₀ : Subgroup G) (p : ℕ) : Prop :=
  P₀ ≤ P ∧ Nat.card P₀ = p ∧
    (∀ g : G, uniqueFourConj g P₀ ≤ P → uniqueFourConj g P₀ = P₀) ∧
    (∃ (_ : Fact p.Prime) (n : ℕ), 2 ≤ n ∧
      Nonempty (uniqueFourLayer (Subgroup.centralizer (P₀ : Set G)) ≃*
        PSL(2, GaloisField p n))) ∧
    ¬ uniqueFourLayer (Subgroup.centralizer (P₀ : Set G)) ≤ M ∧
    (∀ S : Subgroup G, S ≤ Subgroup.centralizer (P₀ : Set G) ⊓
        Subgroup.centralizer (uniqueFourLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) →
      IsPGroup p S → IsCyclic S) ∧
    uniqueFourIsFrobenius (uniqueFourPrimeCore p M ⊔ P₀) (pCoreOf 2 M)
      (uniqueFourPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀) ∧
    ∀ P₁ : Subgroup G, P₁ ≤ P → Nat.card P₁ = p → P₁ ≠ P₀ →
      Subgroup.normalizer (P₁ : Set G) ≤ M

@[expose] def uniqueFourAlmostStrong [Finite G] (M : Subgroup G) (p : ℕ) : Prop :=
  p ∈ uniqueFourBeta G ∧ M ≠ ⊤ ∧ IsTwoLocal M ∧
    ∃ P : Sylow p G, (P : Subgroup G) ≤ M ∧ uniqueFourGamma p P ≤ M ∧
      ((p ∣ Nat.card M ∧
          ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ uniqueFourConj g M : Subgroup G)) ∨
        (5 ≤ p ∧ Group.IsSolvable M ∧ IsMulCommutative (P : Subgroup G) ∧
          ∃ P₀ : Subgroup G, uniqueFourClauseTwo M P P₀ p))

@[expose] def uniqueFourUnique (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ M : Subgroup G, uniqueFourIsMaxTwoLocal M → (uniqueFourSigma M).Nonempty →
    (∀ p ∈ uniqueFourSigma M, uniqueFourAlmostStrong M p) ∧
      ∀ H : Subgroup G, IsTwoLocal H → (∃ p ∈ uniqueFourSigma M, 2 ≤ pRank p (H ⊓ M)) →
        H ≤ M

end CFSG.Open
