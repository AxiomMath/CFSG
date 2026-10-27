module

public import CFSG.Quasithin.Recognition.St84.Sec4Setup

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open scoped commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

structure CaseBGen (X : Setup Γ G) : Prop where
  char : CharTwoStab (V := V) (G := G)
  two_le_n : ∀ i : ℤ, 2 ≤ X.n i
  b₀ : X.HasB 0 1
  b₁ : X.HasB 1 1
  R_le : ⁅X.Z 0, X.Z 1⁆ ≤ X.Z 0 ⊓ X.Z 1
  R_ne : ⁅X.Z 0, X.Z 1⁆ ≠ ⊥
  card_S : Nat.card X.S = 2 ^ (2 * X.n 0 + 2 * X.n 1)
  inf_bot : X.Q (-1) ⊓ X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 = ⊥

end Setup

end CFSG.Quasithin.St84

end
