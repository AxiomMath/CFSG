module

public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenBridge
public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenPair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl1911 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∃ I : Subgroup G, I ≤ Z193 D V ∧ Nat.card ↥I = 4 ∧ V₀ ≤ I ∧
    normalizer (Z193 D V : Set G) ≤ normalizer (I : Set G) ∧
    ∃ g ∈ normalizer (Z193 D V : Set G), g ∉ D.M ∧ g ^ 2 ∈ D.M

@[expose] def Gap1911e (D : Data G) (V X : Subgroup G) : Prop :=
  ∃ (g₁ g₂ : G) (K₁ K₂ : Subgroup G) (k₁ k₂ : G), Pair1911 D V X g₁ g₂ K₁ K₂ k₁ k₂ ∧
    Nat.card ↥(Z193 D V) ≤
      2 * Nat.card ↥(Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G)) ∧
    Nat.card ↥(Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G)) ≤
      2 * Nat.card ↥(Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G) ⊓
        centralizer (pairSub (conjSubgroup V g₂) k₂ : Set G))

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem exists_pair1911 (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V') :
    ∃ (g₁ g₂ : G) (K₁ K₂ : Subgroup G) (k₁ k₂ : G), Pair1911 D V X g₁ g₂ K₁ K₂ k₁ k₂ := by
  obtain ⟨g₁, g₂, K₁, K₂, k₁, k₂, h₁, h₂, m₁, m₂, n₁, n₂, hne, l₁, l₂⟩ := c.exists_pair h162 h763
  exact ⟨g₁, g₂, K₁, K₂, k₁, k₂, ⟨h₁, h₂, m₁, m₂, n₁, n₂, hne, l₁, l₂⟩⟩

theorem nineteen_eleven (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    (h2 : Nat.card ↥V₀ = 2) (hgap : Gap1911e D V X) : Concl1911 D V₀ V := by
  obtain ⟨g₁, g₂, K₁, K₂, k₁, k₂, hp, hb₁, hb₂⟩ := hgap
  exact c.exists_plane_Z193 h162 h763 h2 hp hb₁ hb₂

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
