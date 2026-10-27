module

public import CFSG.Quasithin.H13.AS91Sec5Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

@[expose] def Stmt6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∃ t ∈ c.E, t ≠ 1 ∧ (¬ ∃ m ∈ c.G1, m * z * m⁻¹ = t) ∧
      (∀ e ∈ c.E, e ≠ 1 → (∃ m ∈ c.G1, m * z * m⁻¹ = e) ∨ ∃ m ∈ c.G1, m * t * m⁻¹ = e) ∧
      (∀ g : G, t ∈ c.E.map (MulAut.conj g).toMonoidHom →
        c.E.map (MulAut.conj g).toMonoidHom = c.E) ∧
      centralizer ({t} : Set G) = c.G1 ⊓ centralizer ({t} : Set G)

end CFSG.Quasithin.H13.AS91
