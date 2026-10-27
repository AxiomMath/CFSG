module

public import CFSG.Open.Defs
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.Open
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] noncomputable def GLBTwoLocalRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  twoLocalPrimeRank p G

@[expose] def GLBBetaFour (G : Type*) [Group G] [Finite G] : Set ℕ :=
  {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 4 ≤ GLBTwoLocalRank p G}

@[expose] def GLBIsMaxTwoLocal (M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M

@[expose] def GLBConj (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] noncomputable def GLBWeakCore [Finite G] (p : ℕ) (P : Subgroup G) : Subgroup G :=
  rankThreeAschCore 2 p P

@[expose] def GLBWeakCoreLocal (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  3 ≤ pRank p (⊤ : Subgroup G) ∧
    ∀ P : Sylow p G, ∃ H : Subgroup G, IsTwoLocal H ∧ GLBWeakCore p (P : Subgroup G) ≤ H

@[expose] def GLBPreuniqueness (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ q ∈ GLBBetaFour G, GLBWeakCoreLocal G q

@[expose] def GLBStronglyEmbedded (p : ℕ) (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ p ∣ Nat.card M ∧ ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G)

@[expose] def GLBDeltaOne (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ q ∈ GLBBetaFour G, ∀ P : Sylow q G,
    ∃ H : Subgroup G, IsTwoLocal H ∧ GLBCore q 2 (P : Subgroup G) ≤ H

@[expose] def GLBDeltaTwo (G : Type*) [Group G] [Finite G] : Prop :=
  3 ∈ GLBBetaFour G → ∀ P : Sylow 3 G, ∀ M : Subgroup G, GLBIsMaxTwoLocal M →
    (P : Subgroup G) ≤ M →
      GLBStronglyEmbedded 3 M ∨
        (Group.IsSolvable M ∧
          ∀ x ∈ M, orderOf x = 3 →
            3 ≤ pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G)) →
            Subgroup.centralizer ({x} : Set G) ≤ M)

@[expose] def GLBIsBmax [Finite G] (p : ℕ) (B : Subgroup G) : Prop :=
  IsElemAbelian p B ∧ Nat.card B = p ^ GLBTwoLocalRank p G ∧
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)

@[expose] def GLBSigma [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p ∈ GLBBetaFour G ∧ ∃ B : Subgroup G, GLBIsBmax p B ∧ B ≤ M}

@[expose] def GLBPrimeCore (p : ℕ) (H : Subgroup G) : Subgroup G :=
  relPPrimeCore p H

@[expose] def GLBLayer (H : Subgroup G) : Subgroup G :=
  sSup {L | IsComponentOf L H}

@[expose] def GLBIsFrobenius (R K V : Subgroup G) : Prop :=
  K ≠ ⊥ ∧ V ≠ ⊥ ∧ K ≤ R ∧ (K.subgroupOf R).Normal ∧ V ≤ R ∧ R = K ⊔ V ∧ K ⊓ V = ⊥ ∧
    ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1

@[expose] def GLBClauseTwo [Finite G] (M P P₀ : Subgroup G) (p : ℕ) : Prop :=
  P₀ ≤ P ∧ Nat.card P₀ = p ∧
    (∀ g : G, GLBConj g P₀ ≤ P → GLBConj g P₀ = P₀) ∧
    (∃ (_ : Fact p.Prime) (n : ℕ), 2 ≤ n ∧
      Nonempty (GLBLayer (Subgroup.centralizer (P₀ : Set G)) ≃*
        PSL(2, GaloisField p n))) ∧
    ¬ GLBLayer (Subgroup.centralizer (P₀ : Set G)) ≤ M ∧
    (∀ S : Subgroup G, S ≤ Subgroup.centralizer (P₀ : Set G) ⊓
        Subgroup.centralizer (GLBLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) →
      IsPGroup p S → IsCyclic S) ∧
    GLBIsFrobenius (GLBPrimeCore p M ⊔ P₀) (pCoreOf 2 M)
      (GLBPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀) ∧
    ∀ P₁ : Subgroup G, P₁ ≤ P → Nat.card P₁ = p → P₁ ≠ P₀ →
      Subgroup.normalizer (P₁ : Set G) ≤ M

@[expose] def GLBAlmostStrong [Finite G] (M : Subgroup G) (p : ℕ) : Prop :=
  p ∈ GLBBetaFour G ∧ M ≠ ⊤ ∧ IsTwoLocal M ∧
    ∃ P : Sylow p G, (P : Subgroup G) ≤ M ∧ GLBCore p 2 (P : Subgroup G) ≤ M ∧
      ((p ∣ Nat.card M ∧
          ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G)) ∨
        (5 ≤ p ∧ Group.IsSolvable M ∧ IsMulCommutative (P : Subgroup G) ∧
          ∃ P₀ : Subgroup G, GLBClauseTwo M P P₀ p))

@[expose] def GLBUniqueFour (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ M : Subgroup G, GLBIsMaxTwoLocal M → (GLBSigma M).Nonempty →
    (∀ p ∈ GLBSigma M, GLBAlmostStrong M p) ∧
      ∀ H : Subgroup G, IsTwoLocal H → (∃ p ∈ GLBSigma M, 2 ≤ pRank p (H ⊓ M)) →
        H ≤ M

end CFSG.Open