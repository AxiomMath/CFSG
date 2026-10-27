module

public import CFSG.GroupTheory.SteinbergCBHHBIrreducibleCore

public section

namespace CFSG.RepresentationTheory

open scoped commutatorElement

theorem card_quotient_center_le_finrank_sq
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Nontrivial V]
    (ρ : G →* (Module.End k V)ˣ) (hρ : Function.Injective ρ)
    (hscalar : ∀ z ∈ Subgroup.center G, ∃ c : k,
      (ρ z : Module.End k V) = c • 1)
    (hclass : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) :
    Nat.card (G ⧸ Subgroup.center G) ≤ Module.finrank k V ^ 2 := by
  classical
  have hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G := by
    intro s t
    exact hclass t s
  have hli := CFSG.GroupTheory.HallHigmanB.linearIndependent_rho_out ρ hρ hscalar hcl
  have : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
  have hdim := hli.fintype_card_le_finrank
  rw [Module.finrank_linearMap] at hdim
  simpa [Nat.card_eq_fintype_card, pow_two] using hdim

end CFSG.RepresentationTheory
