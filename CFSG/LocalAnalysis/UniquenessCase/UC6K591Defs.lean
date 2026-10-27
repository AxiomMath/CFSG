module

public import CFSG.LocalAnalysis.UniquenessCase.UC6L620Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6O633Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open

namespace UCK

@[expose] def K631 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → ∀ r : ℕ, r.Prime → r ≠ 2 →
    ∀ N : Subgroup Y, N.Normal → IsSimpleGroup ↥N → ¬ IsMulCommutative ↥N →
      centralizer (N : Set Y) = ⊥ → CFSG.Open.pRank r N = 1 →
      ∀ B : Subgroup Y, CFSG.Open.IsElemAbelian r B → B ⊓ N = ⊥ → Nat.card B ≤ r

@[expose] def KSz : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.Open.IsKGroup S → IsSimpleGroup S →
    ¬ IsMulCommutative S → Nat.Coprime 3 (Nat.card S) →
    ∀ α : MulAut S, orderOf α = 3 → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ¬ (p ^ (Nat.card S).factorization p ∣ Nat.card {s : S // α s = s})

@[expose] def LemmaC : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ N D : Subgroup X,
    D ≤ normalizer (N : Set X) → Nat.card D = 3 → Nat.Coprime 3 (Nat.card N) →
    (∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup X, Q ≤ N → IsPGroup q Q →
      D ≤ normalizer (Q : Set X) → Q ≤ centralizer (D : Set X)) →
    ∃ k : ℕ, Nat.card ↥⁅N, D⁆ = 2 ^ k

@[expose] def KTits : Prop :=
  ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .Tits 0 2 1 →
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a

end UCK

namespace UC6

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

noncomputable abbrev EL : Subgroup G := m.A ⊓ m.L

@[expose] def KC633 : Prop :=
  ∀ y ∈ normalizer (m.L : Set G), (∃ k : ℕ, orderOf y = m.r ^ k) →
    (∀ e ∈ m.EL, y * e * y⁻¹ * e⁻¹ ∈ m.OL) →
      ∃ e ∈ m.EL, ⁅zpowers (e⁻¹ * y), m.L⁆ ≤ m.OL

@[expose] def KN633 : Prop :=
  ∀ X : Subgroup G, X ≤ normalizer (m.L : Set G) → m.EL ≤ normalizer (X : Set G) →
    (∀ y ∈ X, (∃ k : ℕ, orderOf y = m.r ^ k) → ⁅zpowers y, m.L⁆ ≤ m.OL) →
      (∀ x ∈ X, ∀ e ∈ m.EL, x * e * x⁻¹ * e⁻¹ ∈ m.OL) ∧
        (⁅X, m.L⁆ ≤ m.OL ∨ (m.r = 3 ∧ CFSG.Blueprint.LieModel m.Lbar .PSL 3 2 2))

@[expose] def KInv633 : Prop :=
  ∀ x ∈ normalizer (m.L : Set G), ∀ y ∈ normalizer (m.L : Set G),
    (∃ k : ℕ, orderOf x = 2 ^ k) → (∃ k : ℕ, orderOf y = 2 ^ k) →
    (∀ e ∈ m.EL, x * e * x⁻¹ * e⁻¹ ∈ m.OL) → (∀ e ∈ m.EL, y * e * y⁻¹ * e⁻¹ ∈ m.OL) →
    ¬ ⁅zpowers x, m.L⁆ ≤ m.OL → ¬ ⁅zpowers y, m.L⁆ ≤ m.OL →
      ⁅zpowers (x⁻¹ * y), m.L⁆ ≤ m.OL

@[expose] def C628a' : Prop :=
  m.V ⊓ centralizer (m.Z : Set G) = ⊥ → ⁅m.Z, m.U⁆ ≤ CFSG.Open.pCoreOf 2 m.K

end Mz614

end UC6

end CFSG.LocalAnalysis.UniquenessCase
