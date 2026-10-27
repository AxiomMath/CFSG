module

public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def HFixSylow82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H S : Subgroup (MulAut V)),
    (BinaryNineTensor H ⊤ ⊥ 1 ∨ MathieuCode22 H ⊤ ⊥ ∨ MathieuCode24 H ⊤ ⊥ ∨
      MathieuCocode24 H ⊤ ⊥) →
      S ≤ H → Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2 → Nat.card ↥(fixV S) ≤ 2

end CFSG.Quasithin.H13
