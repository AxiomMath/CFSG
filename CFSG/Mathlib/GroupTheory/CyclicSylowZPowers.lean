module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

open Subgroup

theorem zpowers_eq_of_commute_of_orderOf_eq_of_isCyclic_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hSylow : ∀ P : Sylow p G, IsCyclic (P : Subgroup G))
    {x y : G} (hx : orderOf x = p) (hy : orderOf y = p) (hcomm : Commute x y) :
    zpowers x = zpowers y := by
  let H : Subgroup G := zpowers x ⊔ zpowers y
  have hpx : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hpy : IsPGroup p (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hnorm : zpowers x ≤ normalizer (zpowers y : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    apply zpowers_le.mpr
    apply mem_centralizer_iff.mpr
    intro z hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    exact (hcomm.zpow_right n).eq.symm
  have hH : IsPGroup p H := hpx.to_sup_of_normal_right' hpy hnorm
  obtain ⟨P, hHP⟩ := hH.exists_le_sylow
  let : IsCyclic (P : Subgroup G) := hSylow P
  let : IsCyclic H := isCyclic_of_injective (Subgroup.inclusion hHP)
    (Subgroup.inclusion_injective hHP)
  let xH : H := ⟨x, (le_sup_left : zpowers x ≤ H) (mem_zpowers x)⟩
  let yH : H := ⟨y, (le_sup_right : zpowers y ≤ H) (mem_zpowers y)⟩
  have hxH : orderOf xH = p :=
    (orderOf_injective H.subtype H.subtype_injective xH).symm.trans hx
  have hyH : orderOf yH = p :=
    (orderOf_injective H.subtype H.subtype_injective yH).symm.trans hy
  have hEq : zpowers xH = zpowers yH := by
    apply IsCyclic.subgroup_eq_iff_card_eq.mpr
    simp only [Nat.card_zpowers, hxH, hyH]
  have hmap := congrArg (fun S : Subgroup H => S.map H.subtype) hEq
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
  exact hmap

end CFSG.GroupTheory
