module

public import CFSG.Quasithin.EmptyFaithful.SzN29G94

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.G11

namespace SzN31

@[expose] def KCFor {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (Γ : Subgroup (GLV V)) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P B : Subgroup (GLV V), P ≤ Γ → B ≤ Γ → IsPGroup p P →
    (∀ b ∈ B, b * b = 1 ∧ ∀ c ∈ B, b * c = c * b) → (∀ b ∈ B, ∀ x ∈ P, b * x * b⁻¹ ∈ P) →
      Nat.card B ≤ 4 * Nat.card ↥(B ⊓ Subgroup.centralizer (P : Set (GLV V)))

@[expose] def G94KC : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ : Subgroup (GLV V)),
    IsQuotientOfSQTKTauCeti ↥Γ → KCFor Γ

@[expose] def G94Counting : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A : Subgroup (GLV V)) (m : ℕ),
    G11.G94Hyp Γ A m → Group.IsSolvable ↥Γ → KCFor Γ → m ≤ 2

@[expose] def G94Small : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A : Subgroup (GLV V)) (m : ℕ),
    G11.G94Hyp Γ A m → Group.IsSolvable ↥Γ → KCFor Γ → m ≤ 2 → G11.G94Concl Γ A m

theorem g94StmtSolv_of_kc_counting_small (hkc : G94KC) (hc : G94Counting) (hs : G94Small) :
    SzN29.G94StmtSolv := by
  intro V _ _ _ Γ A m hyp hsolv
  have hk : KCFor Γ := hkc V Γ hyp.quotient
  exact hs V Γ A m hyp hsolv hk (hc V Γ A m hyp hsolv hk)

end SzN31

end CFSG.Quasithin
