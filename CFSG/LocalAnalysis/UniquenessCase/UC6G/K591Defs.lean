module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.L620Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.O633Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open

namespace UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

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

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
