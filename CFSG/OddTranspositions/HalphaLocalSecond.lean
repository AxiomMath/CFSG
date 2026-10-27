module

public import CFSG.OddTranspositions.HalphaQuotient

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_of_commute_mk_of_ne_H (hC : HypothesisC D)
    {a b : Halpha D hC.alpha} (ha : a ∈ DstarH hC) (hb : b ∈ DstarH hC)
    (hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b))
    (hne : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) :
    Commute a b :=
  commute_of_commute_of_ne (DstarH_isOddTransp hC) ha hb hne hcomm

theorem localSecond_imageClass (hC : HypothesisC D) (hL : LocalSecond D)
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    LocalSecond (imageClass hC) := by
  classical
  let H : Subgroup G := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  intro d hd x y t hxd hyd htd htri'
  obtain ⟨d0, hd0H, rfl⟩ := hd
  obtain ⟨x0, hx0H, rfl⟩ := htri'.1
  obtain ⟨t0, ht0H, rfl⟩ := htri'.2.1
  obtain ⟨y0, hy0H, rfl⟩ := htri'.2.2.1
  have hx0D : (x0 : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx0H)
  have ht0D : (t0 : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp ht0H)
  have hy0D : (y0 : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hy0H)
  have hd0D : (d0 : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hd0H)
  have hxne : mk x0 ≠ mk d0 := by
    intro hEq
    apply htri'.2.2.2.2.2.1
    have h := hyd
    rw [← hEq] at h
    exact h.symm
  have hyne : mk y0 ≠ mk d0 := by
    intro hEq
    apply htri'.2.2.2.2.2.1
    have h := hxd
    rw [← hEq] at h
    exact h
  have htne : mk t0 ≠ mk d0 := by
    intro hEq
    apply htri'.2.2.2.2.2.2
    have h := hyd
    rw [← hEq] at h
    exact h.symm
  have hxtne : mk x0 ≠ mk t0 := by
    intro hEq
    exact htri'.2.2.2.1 hEq
  have hxd' : Commute x0 d0 :=
    commute_of_commute_mk_of_ne_H hC hx0H hd0H hxd hxne
  have hyd' : Commute y0 d0 :=
    commute_of_commute_mk_of_ne_H hC hy0H hd0H hyd hyne
  have htd' : Commute t0 d0 :=
    commute_of_commute_mk_of_ne_H hC ht0H hd0H htd htne
  have hxt' : Commute x0 t0 :=
    commute_of_commute_mk_of_ne_H hC hx0H ht0H htri'.2.2.2.2.1 hxtne
  have htri0 : IsTriangle D (x0 : G) (y0 : G) (t0 : G) := by
    have hcommH : ∀ {a b : H}, Commute (a : G) (b : G) → Commute a b :=
      fun hc => (commute_iff_eq _ _).mpr (Subtype.ext hc.eq)
    refine ⟨hx0D, ht0D, hy0D, ?_, hxt'.map H.subtype, ?_, ?_⟩
    · intro h
      exact htri'.2.2.2.1 (congrArg mk (Subtype.ext h))
    · intro hc
      exact htri'.2.2.2.2.2.1 ((hcommH hc).map mk)
    · intro hc
      exact htri'.2.2.2.2.2.2 ((hcommH hc).map mk)
  have h4G : orderOf ((x0 : G) * (t0 : G) * (y0 : G)) = 4 :=
    hL d0 hd0D (x0 : G) (y0 : G) (t0 : G)
      (hxd'.map H.subtype) (hyd'.map H.subtype) (htd'.map H.subtype) htri0
  have h4 : orderOf (x0 * t0 * y0 : H) = 4 := by
    rw [← Subgroup.orderOf_coe]
    simpa only [Subgroup.coe_mul] using h4G
  have hdvd : orderOf (mk x0 * mk t0 * mk y0) ∣ 4 := by
    have h := orderOf_map_dvd mk (x0 * t0 * y0)
    rw [show mk (x0 * t0 * y0) = mk x0 * mk t0 * mk y0 by simp only [map_mul]] at h
    rwa [h4] at h
  have hsetup := setup_quotient hC hHns
  have hcases := IsTriangle.orderOf_cases hsetup.oddT hsetup.normal htri'
  rcases hcases with ⟨hodd, hgt⟩ | h4' | ⟨m, hmodd, hm1, hm⟩
  · exfalso
    set o : ℕ := orderOf (mk x0 * mk t0 * mk y0) with ho
    have ho4 : o ≤ 4 := by rw [ho]; exact Nat.le_of_dvd (by norm_num) hdvd
    have ho0 : 0 < o := by rw [ho]; exact orderOf_pos _
    have hodd' : Odd o := by rw [ho]; exact hodd
    have hdvd' : o ∣ 4 := by rw [ho]; exact hdvd
    interval_cases o
    · rcases hodd' with ⟨k, hk⟩; omega
    · rcases hdvd' with ⟨c, hc⟩; omega
    · rcases hodd' with ⟨k, hk⟩; omega
  · exact h4'
  · exfalso
    have hm2 : m ∣ 2 := by
      have h := hdvd
      rw [hm] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h
    have hmle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
    interval_cases m
    · rcases hmodd with ⟨k, hk⟩; omega

end CFSG.OddTranspositions
