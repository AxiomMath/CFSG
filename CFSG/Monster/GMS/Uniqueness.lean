module

public import CFSG.Assembly.Defs
public import CFSG.Monster.GMS.ThreeAFi23

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Group

variable {G : Type} [Group G]

@[expose] def OddTypeOrdersCF (a z₀ : G) : Prop :=
  ∀ x y : G, ∀ k : Fin 3, k ≠ 0 → IsConj a x → y ∈ oddNbr a z₀ x → OddNbrType z₀ x y k →
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) = oddTypeStab k

theorem oddTypeOrders_of
    {a z₀ : G} (hT : ThreeAFi23 a z₀) (hCF : OddTypeOrdersCF a z₀) :
    OddTypeOrders a z₀ := by
  intro x y k hx hy hk
  by_cases h0 : k = 0
  · subst h0
    exact hT.card hx ⟨hy, hk⟩
  · exact hCF x y k h0 hx hy hk

variable [Finite G] {d₀ : B} {a z₀ : G}

end Group

end CFSG.Monster.GMS
