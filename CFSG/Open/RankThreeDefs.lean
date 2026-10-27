module

public import CFSG.Open.Defs
public import CFSG.Open.GeneratedCore
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.Open
open Matrix
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] noncomputable def rankThreeLocalRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  twoLocalPrimeRank p G

open Classical in
@[expose] noncomputable def rankThreeSigmaA (G : Type*) [Group G] [Finite G] : Set ℕ :=
  let S₁ := {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < rankThreeLocalRank p G}
  let S₂ := {p | p.Prime ∧ 5 < p ∧ p ∣ Nat.card G ∧ rankThreeLocalRank p G = 3}
  let S₃ := {p | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ rankThreeLocalRank p G = 3}
  let S₄ := {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ rankThreeLocalRank p G = 3}
  if S₁.Nonempty then S₁ else if S₂.Nonempty then S₂ else if S₃.Nonempty then S₃ else S₄

@[expose] def rankThreeAschCoreLocal (G : Type*) [Group G] [Finite G] (k : ℕ) : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ P : Sylow p G,
    ∃ H : Subgroup G, IsTwoLocal H ∧ rankThreeAschCore k p (P : Subgroup G) ≤ H

@[expose] def rankThreeIsMaxTwoLocal (M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M

@[expose] noncomputable def rankThreeGamma [Finite G] (k p : ℕ) (R : Subgroup G) : Subgroup G :=
  GLBCore p k R

@[expose] def rankThreePrimeCore (p : ℕ) (H : Subgroup G) : Subgroup G :=
  relPPrimeCore p H

@[expose] def rankThreeLayer (H : Subgroup G) : Subgroup G :=
  sSup {L | IsComponentOf L H}

@[expose] def rankThreeConj (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def rankThreeFrobeniusProduct (W K V : Subgroup G) : Prop :=
  ∃ X : Subgroup G, (∀ x, x ∈ X ↔ ∃ a ∈ W, ∃ b ∈ V, x = a * b) ∧
    (∀ x, x ∈ X ↔ ∃ a ∈ K, ∃ b ∈ V, x = a * b) ∧
    K ≠ ⊥ ∧ V ≠ ⊥ ∧ K ≤ X ∧ (K.subgroupOf X).Normal ∧ K ⊓ V = ⊥ ∧
    ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1

@[expose] def rankThreeIsQ8CentralCyclic (H : Subgroup G) (m : ℕ) : Prop :=
  ∃ A B : Subgroup G, Nonempty (A ≃* QuaternionGroup 2) ∧ IsCyclic B ∧ Nat.card B = 2 ^ m ∧
    (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊔ B = H ∧ Nat.card (A ⊓ B : Subgroup G) = 2

@[expose] def rankThreeClauseB [Finite G] (M P : Subgroup G) (p : ℕ) : Prop :=
  5 ≤ p ∧ Group.IsSolvable M ∧
    ∃ P₀ : Subgroup G, P₀ ≤ P ∧ Nat.card P₀ = p ∧
      (∀ g : G, rankThreeConj g P₀ ≤ P → rankThreeConj g P₀ = P₀) ∧
      (∃ (_ : Fact p.Prime) (m : ℕ), 2 ≤ m ∧
        Nonempty (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≃*
          PSL(2, GaloisField p m))) ∧
      ¬ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤ M ∧
      rankThreeFrobeniusProduct (rankThreePrimeCore p M) (pCoreOf 2 M)
        (Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = p → Y ≠ P₀ →
        Subgroup.normalizer (Y : Set G) ≤ M

@[expose] def rankThreeClauseC [Finite G] (M P : Subgroup G) : Prop :=
  Group.IsSolvable M ∧
    Nonempty (P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) ∧
    rankThreeGamma 1 3 (thompsonSubgroup P) ≤ M ∧
    ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = 3 → ¬ Y ≤ thompsonSubgroup P →
      ∃ Q : Subgroup G, Q ≤ rankThreePrimeCore 3 M ∧ IsPGroup 2 Q ∧
        ¬ 2 ∣ (Q.subgroupOf (rankThreePrimeCore 3 M)).index ∧
        P ≤ Subgroup.normalizer (Q : Set G) ∧
        ∃ m : ℕ, 1 ≤ m ∧
          rankThreeIsQ8CentralCyclic (Q ⊓ Subgroup.centralizer (Y : Set G)) m

@[expose] def rankThreeUC (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∃ (P : Sylow p G) (M : Subgroup G),
    rankThreeIsMaxTwoLocal M ∧
    rankThreeGamma 2 p P ≤ M ∧
    (rankThreeGamma 1 p P ≤ M ∨ rankThreeClauseB M P p ∨
      (p = 3 ∧ rankThreeClauseC M P)) ∧
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

noncomputable abbrev rankThreeProjImage {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*}
    [Field K] (H : Subgroup (GL ι K)) : Subgroup (ProjGenLinGroup ι K) :=
  PGLModel.projImage H

noncomputable abbrev rankThreePSL (n : ℕ) (K : Type*) [Field K] :
    Subgroup (ProjGenLinGroup (Fin n) K) :=
  PGLModel.projSL n K

noncomputable abbrev rankThreePSU (n p f : ℕ) [Fact p.Prime] :
    Subgroup (ProjGenLinGroup (Fin n) (GaloisField p (2 * f))) :=
  PGLModel.projSU n p f

abbrev rankThreeSympForm (n : ℕ) (K : Type*) [Field K] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  PGLModel.sympForm n K

noncomputable abbrev rankThreePSp (n : ℕ) (K : Type*) [Field K] :
    Subgroup (ProjGenLinGroup (Fin n ⊕ Fin n) K) :=
  PGLModel.projSp n K

abbrev rankThreeMinusQuadForm (m : ℕ) {K : Type*} [Field K] (b c : K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) : K :=
  PGLModel.minusQuadForm m b c v

noncomputable abbrev rankThreeOrthogonalMinus (m : ℕ) (K : Type*) [Field K] (b c : K) :
    Subgroup (GL (Fin m ⊕ Fin m ⊕ Fin 2) K) :=
  PGLModel.orthogonalMinus m K b c

noncomputable abbrev rankThreePOmegaMinus (m : ℕ) (K : Type*) [Field K] (b c : K) :
    Subgroup (ProjGenLinGroup (Fin m ⊕ Fin m ⊕ Fin 2) K) :=
  PGLModel.projOmegaMinus m K b c

abbrev rankThreeIModel (G : Type*) [Group G] : Prop :=
  PGLModel.IModel G

end CFSG.Open