module

public import CFSG.OddTranspositions.HalphaLocalSecond

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem orderOf_eq_four_of_isTriangle_imageClass (hC : HypothesisC D) (hL : LocalSecond D)
    (hHns : ¬ Group.IsSolvable ↥(Halpha D hC.alpha)) {x y t : ↥(Halpha D hC.alpha) ⧸ CFSG.solvableRadical ↥(Halpha D hC.alpha)}
    (h : IsTriangle (imageClass hC) x y t) : orderOf (x * t * y) = 4 := by
  classical
  let H : Subgroup G := Halpha D hC.alpha
  let mk := QuotientGroup.mk' (CFSG.solvableRadical H)
  have hsetup := setup_quotient hC hHns
  have hcases := IsTriangle.orderOf_cases hsetup.oddT hsetup.normal h
  obtain ⟨x0, hx0H, rfl⟩ := h.1
  obtain ⟨t0, ht0H, rfl⟩ := h.2.1
  obtain ⟨y0, hy0H, rfl⟩ := h.2.2.1
  have hx0 := (mem_DstarH_iff hC).mp hx0H
  have ht0 := (mem_DstarH_iff hC).mp ht0H
  have hy0 := (mem_DstarH_iff hC).mp hy0H
  have hxt' : Commute x0 t0 :=
    commute_of_commute_mk_of_ne_H hC hx0H ht0H h.2.2.2.2.1 h.2.2.2.1
  have htri0 : IsTriangle D (x0 : G) (y0 : G) (t0 : G) := by
    have hcommH : ∀ {a b : H}, Commute (a : G) (b : G) → Commute a b :=
      fun hc => (commute_iff_eq _ _).mpr (Subtype.ext hc.eq)
    refine ⟨DalphaStar_subset hC.isBlock_alpha hx0, DalphaStar_subset hC.isBlock_alpha ht0,
      DalphaStar_subset hC.isBlock_alpha hy0, ?_, hxt'.map H.subtype, ?_, ?_⟩
    · intro hEq
      exact h.2.2.2.1 (congrArg mk (Subtype.ext hEq))
    · intro hc
      exact h.2.2.2.2.2.1 ((hcommH hc).map mk)
    · intro hc
      exact h.2.2.2.2.2.2 ((hcommH hc).map mk)
  have h4G : orderOf ((x0 : G) * (t0 : G) * (y0 : G)) = 4 :=
    hL hC.d hC.hd (x0 : G) (y0 : G) (t0 : G) (hC.DalphaStar_subset_commute hx0).2
      (hC.DalphaStar_subset_commute hy0).2 (hC.DalphaStar_subset_commute ht0).2 htri0
  have h4 : orderOf (x0 * t0 * y0 : H) = 4 := by
    rw [← Subgroup.orderOf_coe]
    simpa only [Subgroup.coe_mul] using h4G
  have hdvd : orderOf (mk x0 * mk t0 * mk y0) ∣ 4 := by
    have h' := orderOf_map_dvd mk (x0 * t0 * y0)
    rw [show mk (x0 * t0 * y0) = mk x0 * mk t0 * mk y0 by simp only [map_mul]] at h'
    rwa [h4] at h'
  rcases hcases with ⟨hodd, hgt⟩ | h4' | ⟨m, hmodd, hm1, hm⟩
  · exfalso
    set o : ℕ := orderOf (mk x0 * mk t0 * mk y0) with ho
    have ho4 : o ≤ 4 := by rw [ho]; exact Nat.le_of_dvd (by norm_num) hdvd
    have hodd' : Odd o := by rw [ho]; exact hodd
    have hdvd' : o ∣ 4 := by rw [ho]; exact hdvd
    have hgt' : 1 < o := by rw [ho]; exact hgt
    interval_cases o
    · rcases hodd' with ⟨k, hk⟩; omega
    · rcases hdvd' with ⟨c, hc⟩; omega
    · rcases hodd' with ⟨k, hk⟩; omega
  · exact h4'
  · exfalso
    have hm2 : m ∣ 2 := by
      have h' := hdvd
      rw [hm] at h'
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h'
    have hmle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
    interval_cases m
    · rcases hmodd with ⟨k, hk⟩; omega

end CFSG.OddTranspositions

end
