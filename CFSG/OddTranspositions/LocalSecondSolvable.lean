module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.SevenLocalSecondConverse

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem localSecond_of_isSolvable_Halpha (hC : HypothesisC D)
    (hsolv : Group.IsSolvable (Halpha D hC.alpha)) : LocalSecond D := by
  have hN : CFSG.Timmesfeld.Connectivity.IsNormalSet (DstarH hC) := fun _ _ ha =>
    DstarH_conj_mem hC ha
  refine localSecond_of_DalphaStar_triangles hC fun x hx y hy t ht htri => ?_
  let x' : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  let y' : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
  let t' : Halpha D hC.alpha := ⟨t, Subgroup.subset_closure ht⟩
  have hc : ∀ a b : Halpha D hC.alpha, Commute a b ↔ Commute (a : G) b := fun a b =>
    ⟨fun h => congrArg Subtype.val h.eq, fun h => Subtype.ext h.eq⟩
  have htri' : IsTriangle (DstarH hC) x' y' t' :=
    ⟨hx, ht, hy, fun e => htri.2.2.2.1 (congrArg Subtype.val e),
      (hc x' t').mpr htri.2.2.2.2.1,
      fun h => htri.2.2.2.2.2.1 ((hc x' y').mp h),
      fun h => htri.2.2.2.2.2.2 ((hc t' y').mp h)⟩
  have h4 := triangle_secondKind_of_solvable hN (DstarH_isOddTransp hC)
    (DstarH_closure_eq_top hC) hsolv htri'
  rw [← Subgroup.orderOf_coe] at h4
  exact h4

end CFSG.OddTranspositions
