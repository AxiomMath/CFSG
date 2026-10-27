module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def IsL3U3 (p : ℕ) (K : Type) [Group K] : Prop :=
  (p % 4 = 1 ∧ IsPSU 3 p 1 K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 K)

@[expose] def cenZ {X : Type} [Group X] (K S : Subgroup X) : Subgroup X :=
  K ⊓ Subgroup.centralizer (E2P.zOf S : Set X)

@[expose] def AtomCond {X : Type} [Group X] (T M V : Subgroup X) : Prop :=
  ∀ A : Subgroup X, T ≤ A → A ≤ M → ¬ A ≤ Subgroup.normalizer (V : Set X) →
    (∀ B : Subgroup X, T ≤ B → B ≤ A → B = T ∨ B = A) →
    IsElemAbelian 2 (conjClosure V A)

@[expose] def Case2dStar {X : Type} [Group X] [Finite X] (K T M : Subgroup X) (p : ℕ) : Prop :=
  E2P.ASHyp K T M ∧ p.Prime ∧ p ≠ 2 ∧
    ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥K ∧ E2.InducesOuter T K)) ∧
    M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X)

@[expose] def StarStmtFor (P : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T M V : Subgroup X) (p : ℕ), P p → Case2dStar K T M p →
    IsElemAbelian 2 V → V ≤ T → T ≤ Subgroup.normalizer (V : Set X) → AtomCond T M V →
    V ≤ pCoreOf 2 M

@[expose] def StarStmt : Prop := StarStmtFor fun _ => True

@[expose] def F1Stmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K S : Subgroup X) (p : ℕ), p.Prime → p ≠ 2 →
    IsL3U3 p ↥K → IsSylowTwoOf S K → ∀ E : Subgroup X, IsElemAbelian 2 E → E ≤ S →
    S ≤ Subgroup.normalizer (E : Set X) → E ≤ E2P.zOf S

@[expose] def F2Stmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K S : Subgroup X) (p : ℕ), p.Prime → 11 ≤ p →
    IsL3U3 p ↥K → IsSylowTwoOf S K →
    ∃ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), b ≠ 1 ∧ Odd (orderOf b)

@[expose] def F3Stmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K S : Subgroup X) (p : ℕ), p.Prime → p ≠ 2 →
    IsL3U3 p ↥K → K.Normal → Subgroup.centralizer (K : Set X) = ⊥ → IsSylowTwoOf S K →
    ∀ u : X, u * u = 1 → u ∉ K → u ∈ Subgroup.normalizer (S : Set X) →
    ∀ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), Odd (orderOf b) →
      u * b * u⁻¹ = b⁻¹

@[expose] def F4Stmt : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (p : ℕ), p.Prime → p ≠ 2 → commutator E = ⊤ →
    Odd (Nat.card (Subgroup.center E)) → IsL3U3 p (E ⧸ Subgroup.center E) →
    ∀ v : MulAut E, v * v = 1 →
      (¬ ∃ g : E, ∀ x : E, v x * (g * x * g⁻¹)⁻¹ ∈ Subgroup.center E) →
      ∀ c ∈ Subgroup.center E, v c = c⁻¹

@[expose] def F5Stmt : Prop := StarStmtFor fun p => p = 3 ∨ p = 5 ∨ p = 7

end CFSG.Quasithin.Background.Harris.KFact2d
