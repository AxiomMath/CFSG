module

public import CFSG.Quasithin.Background.HMathieuStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H

@[expose] def HQ82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L X : Subgroup (MulAut V)), Mathieu.IsOver L X →
    ((∃ n : ℕ, 1 ≤ n ∧ BinaryNineTensor L ⊤ ⊥ n) ∨ MathieuCode24 L ⊤ ⊥ ∨
      MathieuCocode24 L ⊤ ⊥ ∨ (MathieuCode22 L ⊤ ⊥ ∧ X = L)) →
      (2 : WithTop ℚ) < qOf X

end CFSG.Quasithin.H13
