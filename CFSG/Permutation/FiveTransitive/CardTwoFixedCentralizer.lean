module

public import CFSG.Permutation.FiveTransitive.OddIndexTwoConjugacy

public section

namespace CFSG

namespace FiveTransitive.CardTwoFixedCentralizer

theorem commute
    {G : Type*} [Group G] (Q : Subgroup G) (x : G)
    (hC : Nat.card ((Subgroup.centralizer ({x} : Set G)).subgroupOf Q) = 2)
    (a : (Subgroup.centralizer ({x} : Set G)).subgroupOf Q)
    (d : Subgroup.normalizer (Q : Set G)) (hd : Commute d.val x) :
    Commute a.val.val d.val := by
  let C := (Subgroup.centralizer ({x} : Set G)).subgroupOf Q
  by_cases ha : a = 1
  · subst a
    exact Commute.one_left _
  let α : MulAut Q := Q.normalizerMonoidHom d
  have hxconj : d.val * x * d.val⁻¹ = x := by
    rw [hd.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hax : Commute a.val.val x := Subgroup.mem_centralizer_singleton_iff.mp a.property
  have hconj : Commute (α a.val).val x := by
    have h := hax.map (MulAut.conj d.val)
    change Commute (d.val * a.val.val * d.val⁻¹) (d.val * x * d.val⁻¹) at h
    rw [hxconj] at h
    exact h
  let b : C := ⟨α a.val, Subgroup.mem_centralizer_singleton_iff.mpr hconj.eq⟩
  rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hC a ha b with hb | hb
  · have he : α a.val = 1 := congrArg Subtype.val hb
    have haone : a.val = 1 := α.injective (he.trans (map_one α).symm)
    exact (ha (Subtype.ext haone)).elim
  · have he := congrArg (fun q : C => q.val.val) hb
    change d.val * a.val.val * d.val⁻¹ = a.val.val at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

end FiveTransitive.CardTwoFixedCentralizer

end CFSG
