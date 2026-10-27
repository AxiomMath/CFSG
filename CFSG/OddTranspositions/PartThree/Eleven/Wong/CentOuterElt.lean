module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentOuterPsi
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiagA5
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import CFSG.GH74.GLS.SP.GenOrder

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem outer_dihedral {s : G} (hs : s = D.a * D.w ∨ s = D.a * D.w * D.v) :
    s ^ 2 = D.u ∧ D.t⁻¹ * s * D.t = s⁻¹ ∧
      D.X = D.A ⊔ closure {s, D.t} ∧ D.A ⊓ closure {s, D.t} = ⊥ ∧
      Nonempty (closure {s, D.t} ≃* DihedralGroup 4) := by
  have hw_inv : D.w⁻¹ = D.w := inv_eq_of_mul_eq_one_right D.w_mul_w
  have hv_inv : D.v⁻¹ = D.v := inv_eq_of_mul_eq_one_right D.v_mul_v
  have hcent_u : ∀ g ∈ D.T, Commute g D.u := fun g hg =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp hg).1
  have hcent_v : ∀ g ∈ D.T, Commute g D.v := fun g hg =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2
  have haT : D.a ∈ D.T := D.a_mem_T
  have hbT : D.b ∈ D.T := D.b_mem_T
  have hwT : D.w ∈ D.T := D.M_le_T (D.W_le_M (subset_closure (by simp)))
  have hav : Commute D.a D.v := hcent_v D.a haT
  have hwv : Commute D.w D.v := hcent_v D.w hwT
  have hau : Commute D.a D.u := hcent_u D.a haT
  have hub : Commute D.u D.b := (hcent_u D.b hbT).symm
  have hb_eq : D.b = D.a * D.u := by
    apply mul_left_cancel (a := D.a)
    rw [D.a_mul_b, ← mul_assoc, ← pow_two, D.a_sq, mul_assoc, ← D.commute_u_v.eq, ← mul_assoc,
      D.u_mul_u, one_mul]
  have hwaw : D.w * D.a * D.w = D.b⁻¹ := by
    have h := D.conj_w_a_and_b.1
    rwa [hw_inv] at h
  have haw_sq : (D.a * D.w) ^ 2 = D.u := by
    rw [pow_two]
    calc (D.a * D.w) * (D.a * D.w) = D.a * (D.w * D.a * D.w) := by group
      _ = D.a * D.b⁻¹ := by rw [hwaw]
      _ = D.a * (D.a * D.u)⁻¹ := by rw [hb_eq]
      _ = D.u := by
        rw [mul_inv_rev, D.u_inv, ← mul_assoc, hau.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm_aw_v : Commute (D.a * D.w) D.v := hav.mul_left hwv
  have hs_sq : s ^ 2 = D.u := by
    rcases hs with rfl | rfl
    · simpa only [pow_two] using haw_sq
    · rw [show D.a * D.w * D.v = (D.a * D.w) * D.v from rfl, hcomm_aw_v.mul_pow, haw_sq,
        pow_two, D.v_mul_v, mul_one]
  have ht_a : D.t⁻¹ * D.a * D.t = D.b := by
    have hr : D.t = D.r * D.u := by
      rw [show D.r = D.t * D.u from rfl, mul_assoc, D.u_mul_u, mul_one]
    calc D.t⁻¹ * D.a * D.t = D.u * (D.r⁻¹ * D.a * D.r) * D.u := by
          rw [hr, mul_inv_rev, D.u_inv]; group
      _ = D.u * D.b * D.u := by rw [D.conj_r_a_and_b.1]
      _ = D.b := by rw [hub.eq, mul_assoc, D.u_mul_u, mul_one]
  have ht_w : D.t⁻¹ * D.w * D.t = D.w := by
    rw [show D.t⁻¹ = D.t from D.t_inv, D.commute_t_w.eq, mul_assoc, D.t_mul_t, mul_one]
  have ht_v : D.t⁻¹ * D.v * D.t = D.v := by
    rw [show D.t⁻¹ = D.t from D.t_inv, D.commute_t_v.eq, mul_assoc, D.t_mul_t, mul_one]
  have hbw : D.b * D.w = D.w * D.a⁻¹ := by
    have hwbw : D.w * D.b * D.w = D.a⁻¹ := by
      have h := D.conj_w_a_and_b.2
      rwa [hw_inv] at h
    calc D.b * D.w = (D.w * D.w) * D.b * D.w := by rw [D.w_mul_w, one_mul]
      _ = D.w * (D.w * D.b * D.w) := by group
      _ = D.w * D.a⁻¹ := by rw [hwbw]
  have hconj : D.t⁻¹ * s * D.t = s⁻¹ := by
    rcases hs with rfl | rfl
    · calc D.t⁻¹ * (D.a * D.w) * D.t
          = (D.t⁻¹ * D.a * D.t) * (D.t⁻¹ * D.w * D.t) := by group
        _ = D.b * D.w := by rw [ht_a, ht_w]
        _ = D.w * D.a⁻¹ := hbw
        _ = (D.a * D.w)⁻¹ := by rw [mul_inv_rev, hw_inv]
    · calc D.t⁻¹ * (D.a * D.w * D.v) * D.t
          = (D.t⁻¹ * D.a * D.t) * (D.t⁻¹ * D.w * D.t) * (D.t⁻¹ * D.v * D.t) := by group
        _ = D.b * D.w * D.v := by rw [ht_a, ht_w, ht_v]
        _ = D.w * D.a⁻¹ * D.v := by rw [hbw]
        _ = D.v * (D.w * D.a⁻¹) := (hwv.mul_left hav.inv_left).eq
        _ = (D.a * D.w * D.v)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hw_inv, hv_inv]
  have hst : s * D.t = D.t * s⁻¹ := by
    have h := hconj
    rw [show D.t⁻¹ = D.t from D.t_inv] at h
    calc s * D.t = (D.t * D.t) * s * D.t := by rw [D.t_mul_t, one_mul]
      _ = D.t * (D.t * s * D.t) := by group
      _ = D.t * s⁻¹ := by rw [h]
  have horder_s : orderOf s = 4 := by
    have hnot : ¬ s ^ 2 = 1 := by
      rw [hs_sq]
      intro h
      have hu := D.orderOf_u
      rw [h, orderOf_one] at hu
      norm_num at hu
    have hfin : s ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs_sq, pow_two, D.u_mul_u]
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
    rwa [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h
  have hs_mem_X : s ∈ D.X := by
    refine mem_centralizer_singleton_iff.mpr ?_
    rw [← hs_sq]
    group
  have ht_mem_X : D.t ∈ D.X := mem_centralizer_singleton_iff.mpr D.t_commute_u.eq
  have ha_inv : D.t * D.t = 1 := D.t_mul_t
  have hb_inv : (D.t * s) * (D.t * s) = 1 := by
    calc (D.t * s) * (D.t * s) = D.t * (s * D.t) * s := by group
      _ = D.t * (D.t * s⁻¹) * s := by rw [hst]
      _ = 1 := by rw [← mul_assoc, D.t_mul_t, one_mul, inv_mul_cancel]
  have ha1 : D.t ≠ 1 := by
    intro h
    have ht := D.orderOf_t
    rw [h, orderOf_one] at ht
    norm_num at ht
  have hb1 : D.t * s ≠ 1 := by
    intro h
    have hs_eq_t : s = D.t := by
      calc s = D.t * (D.t * s) := by rw [← mul_assoc, D.t_mul_t, one_mul]
        _ = D.t * 1 := by rw [h]
        _ = D.t := mul_one _
    have hu : D.u = 1 := by rw [← hs_sq, hs_eq_t, pow_two, D.t_mul_t]
    have hu' := D.orderOf_u
    rw [hu, orderOf_one] at hu'
    norm_num at hu'
  have hb_def : D.t * (D.t * s) = s := by rw [← mul_assoc, D.t_mul_t, one_mul]
  have hn : orderOf (D.t * (D.t * s)) = 4 := by rw [hb_def, horder_s]
  let f : DihedralGroup 4 →* G := TauCeti.dihedralHom ha_inv hb_inv hn
  have hf_inj : Function.Injective f := by
    change Function.Injective (TauCeti.dihedralHom ha_inv hb_inv hn)
    exact TauCeti.dihedralHom_injective ha_inv hb_inv ha1 hb1 hn
  have hclosure_eq : closure ({D.t, D.t * s} : Set G) = closure {s, D.t} := by
    apply le_antisymm
    · refine (closure_le _).mpr ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact subset_closure (by simp)
      · rw [hy]
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · refine (closure_le _).mpr ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        have h : D.t * (D.t * s) ∈ closure {D.t, D.t * s} :=
          mul_mem (subset_closure (by simp)) (subset_closure (by simp))
        rwa [hb_def] at h
      · rw [hy]
        exact subset_closure (by simp)
  have hf_range : f.range = closure {s, D.t} := by
    change (TauCeti.dihedralHom ha_inv hb_inv hn).range = closure {s, D.t}
    rw [TauCeti.range_dihedralHom ha_inv hb_inv hn, hclosure_eq]
  have hf_r0 : f (DihedralGroup.r 0) = 1 := by
    change TauCeti.dihedralHom ha_inv hb_inv hn (DihedralGroup.r 0) = 1
    rw [TauCeti.dihedralHom_r]
    simp
  have hf_r2 : f (DihedralGroup.r 2) = D.u := by
    change TauCeti.dihedralHom ha_inv hb_inv hn (DihedralGroup.r 2) = D.u
    rw [TauCeti.dihedralHom_r, hb_def,
      show (ZMod.cast (2 : ZMod 4) : ℤ) = 2 by decide, zpow_two]
    simpa [pow_two] using hs_sq
  have hf_sr0 : f (DihedralGroup.sr 0) = D.t := by
    change TauCeti.dihedralHom ha_inv hb_inv hn (DihedralGroup.sr 0) = D.t
    rw [TauCeti.dihedralHom_sr]
    simp
  have hf_sr2 : f (DihedralGroup.sr 2) = D.t * D.u := by
    change TauCeti.dihedralHom ha_inv hb_inv hn (DihedralGroup.sr 2) = D.t * D.u
    rw [TauCeti.dihedralHom_sr, hb_def,
      show (ZMod.cast (2 : ZMod 4) : ℤ) = 2 by decide, zpow_two]
    rw [show s * s = D.u by simpa [pow_two] using hs_sq]
  have hcent_decide : ∀ z : DihedralGroup 4,
      z * DihedralGroup.sr 0 = DihedralGroup.sr 0 * z →
        z = DihedralGroup.r 0 ∨ z = DihedralGroup.r 2 ∨ z = DihedralGroup.sr 0 ∨
          z = DihedralGroup.sr 2 := by decide
  have hcent_class : ∀ x ∈ closure {s, D.t},
      x ∈ centralizer {D.t} → x ∈ closure {D.u, D.t} := by
    intro x hxK hxC
    have hxrange : x ∈ f.range := by rw [hf_range]; exact hxK
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hxrange
    rw [← hz] at hxC ⊢
    have hzt : z * DihedralGroup.sr 0 = DihedralGroup.sr 0 * z := by
      apply hf_inj
      simp only [map_mul, hf_sr0]
      exact mem_centralizer_singleton_iff.mp hxC
    rcases hcent_decide z hzt with h0 | h2 | hs0 | hs2
    · rw [h0, hf_r0]
      exact one_mem _
    · rw [h2, hf_r2]
      exact subset_closure (by simp)
    · rw [hs0, hf_sr0]
      exact subset_closure (by simp)
    · rw [hs2, hf_sr2]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hA_inf_ut : D.A ⊓ closure {D.u, D.t} = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    obtain ⟨hgA, hgut⟩ := mem_inf.mp hg
    rcases mem_closure_pair D.orderOf_u D.orderOf_t D.t_commute_u.symm hgut with
      rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact absurd (D.A_le_K hgA) D.u_not_mem
    · obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hgA
      exact absurd hy.symm (D.t_ne_d y)
    · exact absurd (D.A_le_K (by rw [← D.t_commute_u.eq] at hgA; exact hgA))
        D.t_mul_u_not_mem_K
  have hinf : D.A ⊓ closure {s, D.t} = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    obtain ⟨hgA, hgK⟩ := mem_inf.mp hg
    have hgC : g ∈ centralizer {D.t} := by
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hgA
      exact mem_centralizer_singleton_iff.mpr (D.d_commute_t y).eq
    exact hA_inf_ut.le (mem_inf.mpr ⟨hgA, hcent_class g hgK hgC⟩)
  have hdihedral : Nonempty (closure {s, D.t} ≃* DihedralGroup 4) := by
    let F : DihedralGroup 4 →* closure {s, D.t} :=
      f.codRestrict _ fun z => hf_range ▸ MonoidHom.mem_range.mpr ⟨z, rfl⟩
    have hF_inj : Function.Injective F := fun z w h => hf_inj (Subtype.ext_iff.mp h)
    have hF_surj : Function.Surjective F := fun y => by
      have hy : (y : G) ∈ f.range := hf_range.symm ▸ y.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hy
      exact ⟨z, Subtype.ext hz⟩
    exact ⟨(MulEquiv.ofBijective F ⟨hF_inj, hF_surj⟩).symm⟩
  have hcard_A : Nat.card D.A = 60 := by
    obtain ⟨e⟩ := D.toSwapData.nonempty_A_mulEquiv_alt5
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcard_K : Nat.card (closure {s, D.t}) = 8 := by
    obtain ⟨e⟩ := hdihedral
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hsup_le : D.A ⊔ closure {s, D.t} ≤ D.X := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (D.d_commute_u y).eq
    · refine (closure_le _).mpr ?_
      rintro x (rfl | rfl)
      exacts [hs_mem_X, ht_mem_X]
  have hsup_card : Nat.card (D.A ⊔ closure {s, D.t} : Subgroup G) = 480 := by
    have hnorm : closure {s, D.t} ≤ normalizer (D.A : Set G) :=
      (le_sup_right : closure {s, D.t} ≤ D.A ⊔ closure {s, D.t}).trans
        (hsup_le.trans (D.second_centralizer_card_and_diagonal_normal).2.1)
    rw [CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hnorm hinf, hcard_A, hcard_K]
  have hsup : D.X = D.A ⊔ closure {s, D.t} :=
    (Subgroup.eq_of_le_of_card_ge hsup_le
      (by rw [hsup_card, (D.second_centralizer_card_and_diagonal_normal).1])).symm
  exact ⟨hs_sq, hconj, hsup, hinf, hdihedral⟩

theorem normalized_outer_element :
    ∃ s : G, (s = D.a * D.w ∨ s = D.a * D.w * D.v) ∧
      s ^ 2 = D.u ∧ D.t⁻¹ * s * D.t = s⁻¹ ∧
      D.X = D.A ⊔ closure {s, D.t} ∧ D.A ⊓ closure {s, D.t} = ⊥ ∧
      Nonempty (closure {s, D.t} ≃* DihedralGroup 4) ∧
      ∀ x x' : SL5, psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
        (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM → s⁻¹ * D.d x * s = D.d x' := by
  obtain ⟨s, hs, hpsi⟩ := D.exists_outer_psi
  obtain ⟨hs2, ht, hX, hA, hD⟩ := D.outer_dihedral hs
  exact ⟨s, hs, hs2, ht, hX, hA, hD, hpsi⟩

end CFSG.OddTranspositions.PartThree.Wong.SplitData
