module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.KGC31

@[expose] def NoM22SectionLieExc : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (∃ f : ℕ, (2 ≤ f ∧ IsG2 2 f S) ∨ (1 ≤ f ∧ Is3D4 2 f S) ∨ (Odd f ∧ 3 ≤ f ∧ Is2F4 f S)) →
    ∀ (Y : Subgroup S) (φ : ↥Y →* CFSG.Blueprint.NativeSporadic.Carrier .M22),
      ¬ Function.Surjective φ

end CFSG.Quasithin.KGC31

end
