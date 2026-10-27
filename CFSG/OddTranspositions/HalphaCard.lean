module

public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.WidthSylow

public section

namespace CFSG.OddTranspositions

variable {G : Type} [Group G] [Finite G] {D : Set G}

variable (hC : HypothesisC D)

theorem Halpha_ne_top (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    Halpha D hC.alpha ≠ ⊤ := by
  intro htop
  have hd_comm : ∀ x ∈ Halpha D hC.alpha, Commute hC.d x := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => Commute hC.d y) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact (hC.DalphaStar_subset_commute hy).2.symm
    · exact Commute.one_right hC.d
    · intro y z _ _ ihy ihz
      exact ihy.mul_right ihz
    · intro y _ ihy
      exact ihy.inv_right
  have hd_center : hC.d ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hd_comm g (htop ▸ Subgroup.mem_top g)).eq.symm
  have hcenter : Subgroup.center G = ⊥ :=
    center_eq_bot_of_solvableRadical_eq_bot
      (hrad (CFSG.solvableRadical G) inferInstance
        CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical)
  have hd_one : hC.d = 1 := by
    have hmem : hC.d ∈ (⊥ : Subgroup G) := hcenter ▸ hd_center
    simpa using hmem
  have hd_order : orderOf hC.d = 2 :=
    hC.setup.oddT.1 hC.d (hC.isBlock_alpha.subset hC.d_mem_alpha)
  rw [hd_one, orderOf_one] at hd_order
  omega

theorem card_Halpha_lt (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    Nat.card (Halpha D hC.alpha) < Nat.card G := by
  have hlt : Halpha D hC.alpha < ⊤ :=
    lt_of_le_of_ne le_top (Halpha_ne_top hC hrad)
  have hcard := Subgroup.card_lt_of_lt hlt
  rwa [Subgroup.card_top] at hcard

theorem card_quotient_Halpha_lt
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    Nat.card (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) < Nat.card G := by
  have hle : Nat.card (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
      ≤ Nat.card (Halpha D hC.alpha) :=
    Nat.card_le_card_of_surjective
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      (QuotientGroup.mk'_surjective (CFSG.solvableRadical (Halpha D hC.alpha)))
  exact lt_of_le_of_lt hle (card_Halpha_lt hC hrad)

end CFSG.OddTranspositions
