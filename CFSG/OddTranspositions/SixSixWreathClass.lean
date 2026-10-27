module

public import CFSG.Timmesfeld.Bridge.Asc72WIso
public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_l2Wreath_class_of_not_isSimpleGroup_minimalNormal
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {M : Subgroup G} (hM : Asc72.IsMinimalNormal M) (hMns : ¬ IsSimpleGroup M) :
    ∃ f n : ℕ, 2 ≤ f ∧ ∃ Φ : G ≃* L2Wreath f n,
      ∀ u ∈ D, ∃ i j : Fin n, i ≠ j ∧ (Φ u).right = Equiv.swap i j ∧
        (∀ k, k ≠ i → k ≠ j → (Φ u).left k = 1) ∧
        (Φ u).left j = ((Φ u).left i)⁻¹ := by
  haveI : M.Normal := hM.1
  obtain ⟨W⟩ := nonempty_wreathData hC.setup hrad hM hMns
  have hcent : Subgroup.centralizer (M : Set G) = ⊥ :=
    centralizer_eq_bot_of_minimal hC.setup hrad hM
  obtain ⟨f, hf, Φ, hΦ⟩ := W.exists_mulEquiv_l2Wreath hC.setup hcent
  exact ⟨f, W.r, hf, Φ, hΦ⟩

end CFSG.OddTranspositions
