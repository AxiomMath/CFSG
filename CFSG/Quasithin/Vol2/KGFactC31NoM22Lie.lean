module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.KGC31

@[expose] def SQTKLieType (S : Type) [Group S] : Prop :=
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ IsPSL 2 p f S) ∨ IsPSL 3 p 1 S ∨ IsPSU 3 p 1 S)) ∨
  (∃ f : ℕ,
    (2 ≤ f ∧ IsPSL 2 2 f S) ∨ (1 ≤ f ∧ IsPSL 3 2 f S) ∨ (2 ≤ f ∧ IsPSU 3 2 f S) ∨
    (2 ≤ f ∧ IsPSp4 2 f S) ∨ (2 ≤ f ∧ IsG2 2 f S) ∨ (1 ≤ f ∧ Is3D4 2 f S) ∨
    (Odd f ∧ 3 ≤ f ∧ Is2F4 f S) ∨ (Odd f ∧ 3 ≤ f ∧ IsSz f S)) ∨
  IsTits S

@[expose] def A36SLEps3 (S : Type) [Group S] : Prop :=
  ∃ (s : Bool) (p e : ℕ), p.Prime ∧ 1 ≤ e ∧
    ((p = 2 ∧ Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1)) ∨ (p ≠ 2 ∧ e = 1)) ∧
    IsSLEps3 s (p ^ e) S

@[expose] def NoM22SectionLie : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (SQTKLieType S ∨ A36SLEps3 S) →
    ∀ (Y : Subgroup S) (φ : ↥Y →* CFSG.Blueprint.NativeSporadic.Carrier .M22),
      ¬ Function.Surjective φ

end CFSG.Quasithin.KGC31

end
