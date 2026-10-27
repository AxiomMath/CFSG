module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

@[expose] def GGF4NbrAutReflKGInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G), p.Prime → p ≠ 2 →
    IsElemAbelian p Bs → (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) →
    LargeEvenMarking X (fun lab _ _ I _ θ => lab.tag = .F4 ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    Nat.card Bs = p ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) →
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer X Bs) ∧
      GGReflGenerated p (ggAutomizer X Bs) ∧
      ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.centralizer (X : Set G)

@[expose] def GGF4NbrAutReflXiKGInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G), p.Prime → p ≠ 2 →
    IsElemAbelian p Bs → (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) →
    LargeEvenMarking X (fun lab _ _ I _ θ => lab.tag = .F4 ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    Nat.card Bs = p ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) →
    (∃ ξ ∈ Bs, ∃ (e : ℕ) (Y : Subgroup G) (ψ : StatedSp 3 (GaloisField 2 e) →* G),
      Function.Injective ψ ∧ ψ.range = Y ∧ Y ≤ X ∧ Y ≤ Subgroup.centralizer ({ξ} : Set G) ∧
      CFSG.Assembly.IsSubnormal Y (X ⊓ Subgroup.centralizer ({ξ} : Set G))) →
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer X Bs) ∧
      GGReflGenerated p (ggAutomizer X Bs) ∧
      ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.centralizer (X : Set G)

theorem ggF4NbrAutReflXiKGInput_of_refl (h : GGF4NbrAutReflKGInput) :
    GGF4NbrAutReflXiKGInput := by
  intro G _ _ p Bs X hp hp2 hBs hSC hmk hcard _
  exact h G p Bs X hp hp2 hBs hSC hmk hcard

end CFSG.StandardType
