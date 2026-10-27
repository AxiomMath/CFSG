module

public import CFSG.Monster.GMS.S35
public import CFSG.Monster.GMS.S4Defs
public import CFSG.Sporadic.Fi23.Pair

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint CFSG.Sporadic.Fi23

variable {G : Type*} [Group G]

@[expose] def ThreeAFi23 (a z₀ : G) : Prop :=
  ∀ b x : G, IsConj a b → x ∈ typeSet a z₀ b .threeA →
    ∃ φ : ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}) ≃*
        NativeSporadic.Fi23,
      ∀ h : ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}),
        (h : G) ∈ twoANbr a b ∩ twoANbr a x ↔ IsConj dFi23 (φ h)

namespace ThreeAFi23

variable {a z₀ : G} (hF : ThreeAFi23 a z₀) {b x : G}
include hF

theorem card (hb : IsConj a b) (hx : x ∈ typeSet a z₀ b .threeA) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}) = oddTypeStab 0 := by
  obtain ⟨φ, -⟩ := hF b x hb hx
  rw [Nat.card_congr φ.toEquiv, card_Fi23]
  rfl

end ThreeAFi23

end CFSG.Monster.GMS
