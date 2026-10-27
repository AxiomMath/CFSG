module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45TorusKnownFormsOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGL45KGLabel p lab → S p lab → LargeEvenLabelAll lab (GGL45TorusKGRaw p lab)

theorem ggL45TorusKnownForms_of_cover (S₁ S₂ S₃ : ℕ → LargeEvenLabel → Prop)
    (hcov : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGL45KGLabel p lab → S₁ p lab ∨ S₂ p lab ∨ S₃ p lab)
    (h₁ : GGL45TorusKnownFormsOn S₁) (h₂ : GGL45TorusKnownFormsOn S₂)
    (h₃ : GGL45TorusKnownFormsOn S₃) : GGL45TorusKnownForms := by
  intro p hp hp2 lab hlab hkg
  rcases hcov p lab hp hp2 hlab hkg with h | h | h
  · exact h₁ p hp hp2 lab hlab hkg h
  · exact h₂ p hp hp2 lab hlab hkg h
  · exact h₃ p hp hp2 lab hlab hkg h

@[expose] def GGL45FamE67 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7)

@[expose] def GGL45FamTypeA (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .twA) ∧ p ∣ lab.rank + 1

@[expose] def GGL45FamNonTorsion (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  match lab.tag with
  | .A | .twA => ¬ p ∣ lab.rank + 1
  | .E6 | .twE6 | .E7 => p ≠ 3
  | .E8 => p ≠ 3 ∧ p ≠ 5
  | .F4 | .twF4 | .twF4der | .triD4 => p ≠ 3
  | _ => True

theorem ggL45KGLabel_cover (p : ℕ) (lab : LargeEvenLabel) (hkg : GGL45KGLabel p lab) :
    GGL45FamNonTorsion p lab ∨ GGL45FamTypeA p lab ∨ GGL45FamE67 p lab := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨h1, h2⟩ := hkg
  cases tag
  case A =>
    by_cases hp : p ∣ rank + 1
    · exact Or.inr (Or.inl ⟨Or.inl rfl, hp⟩)
    · exact Or.inl hp
  case twA =>
    by_cases hp : p ∣ rank + 1
    · exact Or.inr (Or.inl ⟨Or.inr rfl, hp⟩)
    · exact Or.inl hp
  case B => exact Or.inl trivial
  case C => exact Or.inl trivial
  case D => exact Or.inl trivial
  case twD => exact Or.inl trivial
  case G2 => exact Or.inl trivial
  case twB2 => exact Or.inl trivial
  case B2der => exact Or.inl trivial
  case G2der => exact Or.inl trivial
  case E6 =>
    by_cases hp : p = 3
    · exact Or.inr (Or.inr ⟨hp, Or.inl rfl⟩)
    · exact Or.inl hp
  case twE6 =>
    by_cases hp : p = 3
    · exact Or.inr (Or.inr ⟨hp, Or.inr (Or.inl rfl)⟩)
    · exact Or.inl hp
  case E7 =>
    by_cases hp : p = 3
    · exact Or.inr (Or.inr ⟨hp, Or.inr (Or.inr rfl)⟩)
    · exact Or.inl hp
  case E8 => exact Or.inl (h1.resolve_left fun h => h rfl)
  case F4 => exact Or.inl (h2.resolve_left fun h => h.1 rfl)
  case twF4 => exact Or.inl (h2.resolve_left fun h => h.2.1 rfl)
  case twF4der => exact Or.inl (h2.resolve_left fun h => h.2.2.1 rfl)
  case triD4 => exact Or.inl (h2.resolve_left fun h => h.2.2.2 rfl)

theorem ggL45_families_cover (p : ℕ) (lab : LargeEvenLabel) (_ : p.Prime) (_ : p ≠ 2)
    (_ : LargeEvenInLambda2 lab) (hkg : GGL45KGLabel p lab) :
    GGL45FamNonTorsion p lab ∨ GGL45FamTypeA p lab ∨ GGL45FamE67 p lab :=
  ggL45KGLabel_cover p lab hkg

theorem ggL45TorusKnownForms_of_families
    (h₁ : GGL45TorusKnownFormsOn GGL45FamNonTorsion) (h₂ : GGL45TorusKnownFormsOn GGL45FamTypeA)
    (h₃ : GGL45TorusKnownFormsOn GGL45FamE67) : GGL45TorusKnownForms :=
  ggL45TorusKnownForms_of_cover _ _ _ ggL45_families_cover h₁ h₂ h₃

@[expose] def GGL45Eps (lab : LargeEvenLabel) : ℤ :=
  match lab.tag with
  | .A => 1
  | _ => -1

@[expose] def GGL45FamTypeACase2 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45FamTypeA p lab ∧ (p : ℤ) ∣ 2 ^ lab.n - GGL45Eps lab

@[expose] def GGL45FamTypeACase1 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45FamTypeA p lab ∧ ¬ (p : ℤ) ∣ 2 ^ lab.n - GGL45Eps lab

theorem ggL45FamTypeA_split (p : ℕ) (lab : LargeEvenLabel) :
    GGL45FamTypeA p lab → GGL45FamTypeACase1 p lab ∨ GGL45FamTypeACase2 p lab := fun h => by
  by_cases hq : (p : ℤ) ∣ 2 ^ lab.n - GGL45Eps lab
  · exact Or.inr ⟨h, hq⟩
  · exact Or.inl ⟨h, hq⟩

end CFSG.StandardType
