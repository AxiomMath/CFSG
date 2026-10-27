module

public import CFSG.Assembly.LargeEvenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGOddAutInnField (p : ℕ) {R : Type} [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ φ : MulAut R, φ ^ p = 1 → ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f

@[expose] def GGRawDatumAll (lab : LargeEvenLabel) (Q : LargeEvenRawCont) : Prop :=
  ∀ Q₀ : LargeEvenRawCont, CFSG.StandardType.LargeEvenRawDatum lab Q₀ →
    CFSG.StandardType.LargeEvenRawDatum lab fun R _ I F => Q₀ R I F ∧ Q R I F

@[expose] def GGOddAutAt (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRawDatumAll lab fun R _ I F =>
    IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGOddAutInnField p I F

@[expose] def GGOddAutOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S lab →
    ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → GGOddAutAt p lab

theorem GGOddAutOn.mono {S S' : LargeEvenLabel → Prop} (hS : ∀ lab, S' lab → S lab)
    (h : GGOddAutOn S) : GGOddAutOn S' :=
  fun p lab hp hp2 hlab hS' hD => h p lab hp hp2 hlab (hS lab hS') hD

theorem GGOddAutOn.or {S S' : LargeEvenLabel → Prop} (h : GGOddAutOn S) (h' : GGOddAutOn S') :
    GGOddAutOn fun lab => S lab ∨ S' lab := by
  intro p lab hp hp2 hlab hS hD
  rcases hS with hS | hS
  · exact h p lab hp hp2 hlab hS hD
  · exact h' p lab hp hp2 hlab hS hD

theorem ggOddAutOn_true_of {S : LargeEvenLabel → Prop} (h : GGOddAutOn S)
    (h' : GGOddAutOn fun lab => ¬ S lab) : GGOddAutOn fun _ => True := by
  refine (h.or h').mono fun lab _ => ?_
  exact em (S lab)

theorem GGOddAutInnField.mono {p : ℕ} {R : Type} [Group R] {I I' F F' : Set (MulAut R)}
    (hI : I ⊆ I') (hF : Subgroup.closure F ≤ Subgroup.closure F')
    (h : GGOddAutInnField p I F) : GGOddAutInnField p I' F' := by
  intro φ hφ
  obtain ⟨u, hu, f, hf, rfl⟩ := h φ hφ
  exact ⟨u, hI hu, f, hF hf, rfl⟩

namespace Legacy
abbrev GGRawDatumAll := CFSG.StandardType.GGRawDatumAll
abbrev GGOddAutAt := CFSG.StandardType.GGOddAutAt
abbrev GGOddAutOn := CFSG.StandardType.GGOddAutOn
end Legacy

namespace Canonical
@[expose] def GGRawDatumAll (lab : LargeEvenLabel) (Q : LargeEvenRawCont) : Prop :=
  ∀ Q₀ : LargeEvenRawCont, CFSG.Assembly.LargeEvenRawDatum lab Q₀ →
    CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F => Q₀ R I F ∧ Q R I F

@[expose] def GGOddAutAt (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRawDatumAll lab fun R _ I F =>
    IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGOddAutInnField p I F

@[expose] def GGOddAutOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S lab →
    ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → GGOddAutAt p lab
end Canonical

end CFSG.StandardType
