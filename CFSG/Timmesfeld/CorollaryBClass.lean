module

public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.Timmesfeld.Bridge.RootStructQD

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup

section Class

variable {G : Type*} [Group G] {D : Set G}

private def Rel (D : Set G) (d e : G) : Prop := ∃ u ∈ closure D, u * d * u⁻¹ = e

private theorem rel_refl (d : G) : Rel D d d := ⟨1, one_mem _, by group⟩

private theorem rel_symm {d e : G} (h : Rel D d e) : Rel D e d := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u⁻¹, inv_mem hu, by group⟩

private theorem rel_trans {d e f : G} (h₁ : Rel D d e) (h₂ : Rel D e f) : Rel D d f := by
  obtain ⟨u, hu, rfl⟩ := h₁
  obtain ⟨v, hv, rfl⟩ := h₂
  exact ⟨v * u, mul_mem hv hu, by group⟩

private theorem rel_of_odd (hD : IsRootInvolutionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (hodd : Odd (orderOf (d * e))) : Rel D d e := by
  obtain ⟨u, hu, hue⟩ :=
    exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he) hodd
  refine ⟨u, (Subgroup.closure_mono ?_) hu, hue⟩
  intro x hx
  rcases hx with rfl | rfl
  · exact hd
  · exact he

variable [Finite G] (hD : IsRootInvolutionSet D) (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D)
  (hsq : ∀ d ∈ D, ∀ e ∈ D, Commute d e → d ≠ e → d * e ∈ D)
include hD hN hsq

private theorem rel_or_rel {d e b : G} (hd : d ∈ D) (he : e ∈ D) (hb : b ∈ D)
    (hde : Commute d e) (hne : d ≠ e) (hdb : ¬ Commute d b) (hodd : Odd (orderOf (d * b))) :
    Rel D d e ∨ Rel D d (d * e) := by
  have hf := hsq d hd e he hde hne
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hb he with hbe | h4 | ⟨hbe, -⟩
  ·
    exfalso
    have hm1 : orderOf (d * b) ≠ 1 := by
      intro h1
      apply hdb
      rw [orderOf_eq_one_iff] at h1
      rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hb]
    have hc : Commute e (d * b) := hde.symm.mul_right hbe.symm
    have hcop : Nat.Coprime (orderOf e) (orderOf (d * b)) := by
      rw [hD.orderOf_eq_two he]
      exact Nat.coprime_two_left.mpr hodd
    have hord := hc.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [hD.orderOf_eq_two he, ← mul_assoc, ← hde.eq] at hord
    rcases hD.orderOf_mul hf hb with h | h | h <;> rw [hord] at h
    · exact hm1 (by omega)
    · obtain ⟨k, hk⟩ := hodd
      omega
    · exact (Nat.not_even_iff_odd.mpr h) (even_two_mul _)
  · obtain ⟨x, hx, -, -, -, hxd⟩ :=
      Bridge.exists_conj_eq_mul_of_odd_special hD hN hd hb he hdb hodd h4 hde hf
    refine Or.inr ⟨x, subset_closure hx, ?_⟩
    rw [hD.inv_eq hx]
    exact hxd
  · exact Or.inl (rel_trans (rel_of_odd hD hd hb hodd) (rel_of_odd hD hb he hbe))

private theorem rel_of_commute
    (hopp : ∀ d ∈ D, ∃ b ∈ D, ¬ Commute d b ∧ Odd (orderOf (d * b))) {d e : G} (hd : d ∈ D)
    (he : e ∈ D) (hde : Commute d e) (hne : d ≠ e) : Rel D d e := by
  obtain ⟨b, hb, hdb, hodd⟩ := hopp d hd
  obtain ⟨b', hb', heb', hodd'⟩ := hopp e he
  rcases rel_or_rel hD hN hsq hd he hb hde hne hdb hodd with h1 | h1
  · exact h1
  rcases rel_or_rel hD hN hsq he hd hb' hde.symm hne.symm heb' hodd' with h2 | h2
  · exact rel_symm h2
  · rw [← hde.eq] at h2
    exact rel_trans h1 (rel_symm h2)

theorem exists_conj_of_opposite
    (hopp : ∀ d ∈ D, ∃ b ∈ D, ¬ Commute d b ∧ Odd (orderOf (d * b))) :
    ∀ d ∈ D, ∀ e ∈ D, ∃ u ∈ closure D, u * d * u⁻¹ = e := by
  intro d hd e he
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hd he with hde | h4 | ⟨hodd, -⟩
  · by_cases hne : d = e
    · subst hne
      exact rel_refl d
    · exact rel_of_commute hD hN hsq hopp hd he hde hne
  · obtain ⟨hz, hdz, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
    have hne : ∀ {x : G}, Commute x ((d * e) ^ 2) → x ≠ (d * e) ^ 2 → x ∈ D →
        Rel D x ((d * e) ^ 2) := fun hx hne hxD => rel_of_commute hD hN hsq hopp hxD hz hx hne
    have hdz' : d ≠ (d * e) ^ 2 := by
      intro heq
      have hc : Commute d e := heq ▸ hez.symm
      have h2 : (d * e) ^ 2 = 1 :=
        (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he)).mp hc
      have := orderOf_dvd_of_pow_eq_one h2
      rw [h4] at this
      exact absurd this (by norm_num)
    have hez' : e ≠ (d * e) ^ 2 := by
      intro heq
      have hc : Commute d e := heq ▸ hdz
      have h2 : (d * e) ^ 2 = 1 :=
        (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he)).mp hc
      have := orderOf_dvd_of_pow_eq_one h2
      rw [h4] at this
      exact absurd this (by norm_num)
    exact rel_trans (hne hdz hdz' hd) (rel_symm (hne hez hez' he))
  · exact rel_of_odd hD hd he hodd

end Class

variable {X : Type*} [Group X] {t : X}

@[expose] def tIn (t : X) : ↥(normalClosure ({t} : Set X)) :=
  ⟨t, cls_subset t (mem_cls_self t)⟩

theorem tIn_mem_clsIn (t : X) : tIn t ∈ clsIn t := mem_cls_self t

theorem Setup.clsIn_eq [Finite X] (h : Setup t)
    (hopp : ∃ d ∈ cls t, ∃ e ∈ cls t, ¬ Commute d e ∧ Odd (orderOf (d * e))) :
    clsIn t = {u | IsConj (tIn t) u} := by
  have key := exists_conj_of_opposite h.isRootInvolutionSet (fun g x hx => conj_mem_cls g hx)
    (fun d hd e he hde hne => h.mul_mem hd he hde hne) (exists_opposite_of_cls hopp)
  ext u
  constructor
  · intro hu
    obtain ⟨w, hw, hwu⟩ := key t (mem_cls_self t) u hu
    rw [← normalClosure_eq] at hw
    refine isConj_iff.mpr ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    simpa [tIn] using hwu
  · intro hu
    obtain ⟨w, rfl⟩ := isConj_iff.mp hu
    exact conj_mem_clsIn w _ (tIn_mem_clsIn t)

end CFSG.Timmesfeld.CorB
