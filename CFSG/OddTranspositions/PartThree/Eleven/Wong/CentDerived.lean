module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentT
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem T_le_X : D.T ≤ D.X := inf_le_left

theorem commutator_T_eq : (commutator D.T).map D.T.subtype = closure {D.u, D.v} := by
  rw [Subgroup.map_subtype_commutator]
  let H : Subgroup G := closure {D.u, D.v}
  have huT : D.u ∈ D.T :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
      mem_centralizer_singleton_iff.mpr D.commute_u_v.eq⟩
  have hvT : D.v ∈ D.T :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr D.commute_u_v.eq.symm,
      mem_centralizer_singleton_iff.mpr rfl⟩
  have hH_le_T : H ≤ D.T := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    exacts [huT, hvT]
  have hT_cent : H ≤ centralizer (D.T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · refine mem_centralizer_iff.mpr fun t ht => ?_
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp ht).1
    · refine mem_centralizer_iff.mpr fun t ht => ?_
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp ht).2
  let N : Subgroup ↥D.T := H.subgroupOf D.T
  have hN_le_center : N ≤ Subgroup.center ↥D.T := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hT_cent hx) y.1 y.2)
  haveI : N.Normal := Subgroup.normal_of_le_center hN_le_center
  let Q := ↥D.T ⧸ N
  let q : ↥D.T →* Q := QuotientGroup.mk' N
  let gens : Set ↥D.T :=
    {⟨D.a, D.a_mem_T⟩, ⟨D.b, D.b_mem_T⟩, ⟨D.w, D.w_mem_T⟩, ⟨D.r, D.r_mem_T⟩}
  let S : Set Q := {q ⟨D.a, D.a_mem_T⟩, q ⟨D.w, D.w_mem_T⟩, q ⟨D.r, D.r_mem_T⟩}
  have hga2 : q ⟨D.a, D.a_mem_T⟩ * q ⟨D.a, D.a_mem_T⟩ = 1 := by
    rw [← map_mul]
    refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    change D.a * D.a ∈ H
    rw [← pow_two, D.a_sq]
    exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hgab : q ⟨D.a, D.a_mem_T⟩ * q ⟨D.b, D.b_mem_T⟩ = 1 := by
    rw [← map_mul]
    refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    change D.a * D.b ∈ H
    rw [D.a_mul_b]
    exact Subgroup.subset_closure (by simp)
  have hb_eq : q ⟨D.b, D.b_mem_T⟩ = q ⟨D.a, D.a_mem_T⟩ := by
    have h1 : q ⟨D.b, D.b_mem_T⟩ = (q ⟨D.a, D.a_mem_T⟩)⁻¹ :=
      eq_inv_of_mul_eq_one_right hgab
    have h2 : (q ⟨D.a, D.a_mem_T⟩)⁻¹ = q ⟨D.a, D.a_mem_T⟩ :=
      inv_eq_of_mul_eq_one_right hga2
    rw [h1, h2]
  have hgens : closure gens = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have hmain : closure (D.T.subtype '' gens) = closure {D.a, D.b, D.w, D.r} := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> simp
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨⟨D.a, D.a_mem_T⟩, by simp [gens], rfl⟩
        · exact ⟨⟨D.b, D.b_mem_T⟩, by simp [gens], rfl⟩
        · exact ⟨⟨D.w, D.w_mem_T⟩, by simp [gens], rfl⟩
        · exact ⟨⟨D.r, D.r_mem_T⟩, by simp [gens], rfl⟩
    exact hmain.trans D.T_eq_closure.symm
  have hbw : D.w⁻¹ * D.a⁻¹ * D.w = D.b := by
    have h := congrArg Inv.inv D.conj_w_a_and_b.1
    simpa [mul_inv_rev, mul_assoc] using h
  have hbr : D.r⁻¹ * D.a⁻¹ * D.r = D.b⁻¹ := by
    have h := congrArg Inv.inv D.conj_r_a_and_b.1
    simpa [mul_inv_rev, mul_assoc] using h
  have ha1 : D.a⁻¹ = D.a * D.u * D.v := by
    calc D.a⁻¹ = D.a * (D.a * D.a)⁻¹ := by group
      _ = D.a * (D.u * D.v)⁻¹ := by rw [← pow_two, D.a_sq]
      _ = D.a * (D.v⁻¹ * D.u⁻¹) := by rw [mul_inv_rev]
      _ = D.a * (D.v * D.u) := by rw [D.u_inv, inv_eq_of_mul_eq_one_right D.v_mul_v]
      _ = D.a * (D.u * D.v) := by rw [D.commute_u_v.eq]
      _ = D.a * D.u * D.v := by group
  have hba : D.b * D.a⁻¹ = D.u := by
    rw [ha1]
    calc D.b * (D.a * D.u * D.v) = (D.b * D.a) * D.u * D.v := by group
      _ = (D.a * D.b) * D.u * D.v := by rw [D.commute_a_b.eq]
      _ = D.v * D.u * D.v := by rw [D.a_mul_b]
      _ = D.v * (D.u * D.v) := by group
      _ = D.v * (D.v * D.u) := by rw [D.commute_u_v.eq]
      _ = D.u := by rw [← mul_assoc, D.v_mul_v, one_mul]
  have hb1 : D.b⁻¹ = D.v * D.a := by
    have h : D.b = D.a⁻¹ * D.v := by rw [← D.a_mul_b]; group
    rw [h, mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right D.v_mul_v]
  have hbua : D.b⁻¹ * D.a = D.u := by
    rw [hb1]
    calc D.v * D.a * D.a = D.v * (D.a * D.a) := by group
      _ = D.v * (D.u * D.v) := by rw [← pow_two, D.a_sq]
      _ = D.v * (D.v * D.u) := by rw [D.commute_u_v.eq]
      _ = D.u := by rw [← mul_assoc, D.v_mul_v, one_mul]
  have hz_aw : (D.a * D.w) * D.v = D.w * D.a := by
    have h : (D.a * D.w)⁻¹ * (D.w * D.a) = D.v := by
      rw [mul_inv_rev]
      calc D.w⁻¹ * D.a⁻¹ * (D.w * D.a) = (D.w⁻¹ * D.a⁻¹ * D.w) * D.a := by group
        _ = D.b * D.a := by rw [hbw]
        _ = D.v := by rw [← D.commute_a_b.eq, D.a_mul_b]
    calc (D.a * D.w) * D.v = (D.a * D.w) * ((D.a * D.w)⁻¹ * (D.w * D.a)) := by rw [h]
      _ = D.w * D.a := by group
  have hz_ar : (D.a * D.r) * D.u = D.r * D.a := by
    have h : (D.a * D.r)⁻¹ * (D.r * D.a) = D.u := by
      rw [mul_inv_rev]
      calc D.r⁻¹ * D.a⁻¹ * (D.r * D.a) = (D.r⁻¹ * D.a⁻¹ * D.r) * D.a := by group
        _ = D.b⁻¹ * D.a := by rw [hbr]
        _ = D.u := hbua
    calc (D.a * D.r) * D.u = (D.a * D.r) * ((D.a * D.r)⁻¹ * (D.r * D.a)) := by rw [h]
      _ = D.r * D.a := by group
  have h_aw : ⁅D.a, D.w⁆ = D.v := by
    have haw : D.a * D.w = D.w * D.b⁻¹ := by rw [← D.conj_w_a_and_b.1]; group
    calc ⁅D.a, D.w⁆ = D.a * D.w * D.a⁻¹ * D.w⁻¹ := by rw [commutatorElement_def]
      _ = D.w * D.b⁻¹ * D.a⁻¹ * D.w⁻¹ := by rw [haw]
      _ = D.w * (D.b⁻¹ * D.a⁻¹) * D.w⁻¹ := by group
      _ = D.w * D.v * D.w⁻¹ := by
            rw [← mul_inv_rev, D.a_mul_b, inv_eq_of_mul_eq_one_right D.v_mul_v]
      _ = D.v := by
            rw [mem_centralizer_singleton_iff.mp (mem_inf.mp D.w_mem_T).2, mul_inv_cancel_right]
  have h_ar : ⁅D.a, D.r⁆ = D.u := by
    have har : D.a * D.r = D.r * D.b := by rw [← D.conj_r_a_and_b.1]; group
    calc ⁅D.a, D.r⁆ = D.a * D.r * D.a⁻¹ * D.r⁻¹ := by rw [commutatorElement_def]
      _ = D.r * D.b * D.a⁻¹ * D.r⁻¹ := by rw [har]
      _ = D.r * (D.b * D.a⁻¹) * D.r⁻¹ := by group
      _ = D.r * D.u * D.r⁻¹ := by rw [hba]
      _ = D.u := by
            rw [mem_centralizer_singleton_iff.mp (mem_inf.mp D.r_mem_T).1, mul_inv_cancel_right]
  have h_aw_q : Commute (q ⟨D.a, D.a_mem_T⟩) (q ⟨D.w, D.w_mem_T⟩) := by
    show q ⟨D.a, D.a_mem_T⟩ * q ⟨D.w, D.w_mem_T⟩ = q ⟨D.w, D.w_mem_T⟩ * q ⟨D.a, D.a_mem_T⟩
    rw [← map_mul, ← map_mul]
    refine (QuotientGroup.mk'_eq_mk' N).mpr
      ⟨⟨D.v, hvT⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (by simp)), ?_⟩
    exact Subtype.ext hz_aw
  have h_ar_q : Commute (q ⟨D.a, D.a_mem_T⟩) (q ⟨D.r, D.r_mem_T⟩) := by
    show q ⟨D.a, D.a_mem_T⟩ * q ⟨D.r, D.r_mem_T⟩ = q ⟨D.r, D.r_mem_T⟩ * q ⟨D.a, D.a_mem_T⟩
    rw [← map_mul, ← map_mul]
    refine (QuotientGroup.mk'_eq_mk' N).mpr
      ⟨⟨D.u, huT⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (by simp)), ?_⟩
    exact Subtype.ext hz_ar
  have h_wr_q : Commute (q ⟨D.w, D.w_mem_T⟩) (q ⟨D.r, D.r_mem_T⟩) :=
    (show Commute (⟨D.w, D.w_mem_T⟩ : ↥D.T) ⟨D.r, D.r_mem_T⟩ from
      Subtype.ext D.commute_w_r.eq).map q
  have hpair : S.Pairwise Commute := by
    intro x hx y hy _
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact Commute.refl _
    · exact h_aw_q
    · exact h_ar_q
    · exact h_aw_q.symm
    · exact Commute.refl _
    · exact h_wr_q
    · exact h_ar_q.symm
    · exact h_wr_q.symm
    · exact Commute.refl _
  have hS_top : closure S = ⊤ := by
    have h1 : closure (q '' gens) = ⊤ := by
      rw [← MonoidHom.map_closure, hgens,
        Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    have h2 : q '' gens = S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · simp [S]
        · rw [hb_eq]; simp [S]
        · simp [S]
        · simp [S]
      · intro hy
        simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact ⟨⟨D.a, D.a_mem_T⟩, by simp [gens], rfl⟩
        · exact ⟨⟨D.w, D.w_mem_T⟩, by simp [gens], rfl⟩
        · exact ⟨⟨D.r, D.r_mem_T⟩, by simp [gens], rfl⟩
    simpa [h2] using h1
  have hQ : IsMulCommutative Q := by
    haveI : IsMulCommutative (⊤ : Subgroup Q) := by
      rw [← hS_top]
      exact Subgroup.isMulCommutative_closure hpair
    refine IsMulCommutative.of_comm fun x y => ?_
    have h : (Subgroup.topEquiv.symm x) * (Subgroup.topEquiv.symm y) =
        (Subgroup.topEquiv.symm y) * (Subgroup.topEquiv.symm x) := mul_comm' _ _
    simpa using congrArg Subgroup.topEquiv h
  have hcomm : commutator ↥D.T ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp hQ
  have hle : ⁅D.T, D.T⁆ ≤ H := by
    calc ⁅D.T, D.T⁆ = (commutator ↥D.T).map D.T.subtype :=
          (Subgroup.map_subtype_commutator D.T).symm
      _ ≤ N.map D.T.subtype := Subgroup.map_mono hcomm
      _ = H := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH_le_T]
  have hH_le : H ≤ ⁅D.T, D.T⁆ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · rw [← h_ar]
      exact commutator_mem_commutator D.a_mem_T D.r_mem_T
    · rw [← h_aw]
      exact commutator_mem_commutator D.a_mem_T D.w_mem_T
  exact le_antisymm hle hH_le

theorem commutator_M_eq : (commutator D.M).map D.M.subtype = zpowers D.v := by
  rw [Subgroup.map_subtype_commutator]
  let H : Subgroup G := zpowers D.v
  have hH_le_M : H ≤ D.M := Subgroup.zpowers_le.mpr D.v_mem_M
  have hav : D.a * D.v = D.v * D.a := by
    rw [← D.a_mul_b]
    exact ((Commute.refl D.a).mul_right D.commute_a_b).eq
  have hbv : D.b * D.v = D.v * D.b := by
    rw [← D.a_mul_b]
    exact (D.commute_a_b.symm.mul_right (Commute.refl D.b)).eq
  have hM_le_cent : D.M ≤ centralizer ({D.v} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr hav
    · exact mem_centralizer_singleton_iff.mpr hbv
    · exact mem_centralizer_singleton_iff.mpr D.commute_v_w.symm.eq
  have hH_cent : H ≤ centralizer (D.M : Set G) :=
    Subgroup.zpowers_le.mpr (mem_centralizer_iff.mpr fun m hm =>
      mem_centralizer_singleton_iff.mp (hM_le_cent hm))
  let N : Subgroup ↥D.M := H.subgroupOf D.M
  have hN_le_center : N ≤ Subgroup.center ↥D.M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hH_cent hx) y.1 y.2)
  haveI : N.Normal := Subgroup.normal_of_le_center hN_le_center
  let Q := ↥D.M ⧸ N
  let q : ↥D.M →* Q := QuotientGroup.mk' N
  let gens : Set ↥D.M := {⟨D.a, Subgroup.subset_closure (by simp)⟩,
    ⟨D.b, Subgroup.subset_closure (by simp)⟩, ⟨D.w, Subgroup.subset_closure (by simp)⟩}
  let S : Set Q := {q ⟨D.a, Subgroup.subset_closure (by simp)⟩,
    q ⟨D.b, Subgroup.subset_closure (by simp)⟩, q ⟨D.w, Subgroup.subset_closure (by simp)⟩}
  have hgens : closure gens = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    change closure (D.M.subtype '' gens) = closure {D.a, D.b, D.w}
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨D.a, Subgroup.subset_closure (by simp)⟩, by simp [gens], rfl⟩
      · exact ⟨⟨D.b, Subgroup.subset_closure (by simp)⟩, by simp [gens], rfl⟩
      · exact ⟨⟨D.w, Subgroup.subset_closure (by simp)⟩, by simp [gens], rfl⟩
  have hbw : D.w⁻¹ * D.a⁻¹ * D.w = D.b := by
    have h := congrArg Inv.inv D.conj_w_a_and_b.1
    simpa [mul_inv_rev, mul_assoc] using h
  have hz_aw : (D.a * D.w) * D.v = D.w * D.a := by
    have h : (D.a * D.w)⁻¹ * (D.w * D.a) = D.v := by
      rw [mul_inv_rev]
      calc D.w⁻¹ * D.a⁻¹ * (D.w * D.a) = (D.w⁻¹ * D.a⁻¹ * D.w) * D.a := by group
        _ = D.b * D.a := by rw [hbw]
        _ = D.v := by rw [← D.commute_a_b.eq, D.a_mul_b]
    calc (D.a * D.w) * D.v = (D.a * D.w) * ((D.a * D.w)⁻¹ * (D.w * D.a)) := by rw [h]
      _ = D.w * D.a := by group
  have hz_bw : (D.b * D.w) * D.v = D.w * D.b := by
    have h : (D.b * D.w)⁻¹ * (D.w * D.b) = D.v := by
      rw [mul_inv_rev]
      calc D.w⁻¹ * D.b⁻¹ * (D.w * D.b) = (D.w⁻¹ * D.b⁻¹ * D.w) * D.b := by group
        _ = D.a * D.b := by
              rw [show D.w⁻¹ * D.b⁻¹ * D.w = (D.w⁻¹ * D.b * D.w)⁻¹ by group]
              rw [D.conj_w_a_and_b.2, inv_inv]
        _ = D.v := D.a_mul_b
    calc (D.b * D.w) * D.v = (D.b * D.w) * ((D.b * D.w)⁻¹ * (D.w * D.b)) := by rw [h]
      _ = D.w * D.b := by group
  have h_aw : ⁅D.a, D.w⁆ = D.v := by
    have haw : D.a * D.w = D.w * D.b⁻¹ := by rw [← D.conj_w_a_and_b.1]; group
    calc ⁅D.a, D.w⁆ = D.a * D.w * D.a⁻¹ * D.w⁻¹ := by rw [commutatorElement_def]
      _ = D.w * D.b⁻¹ * D.a⁻¹ * D.w⁻¹ := by rw [haw]
      _ = D.w * (D.b⁻¹ * D.a⁻¹) * D.w⁻¹ := by group
      _ = D.w * D.v * D.w⁻¹ := by
            rw [← mul_inv_rev, D.a_mul_b, inv_eq_of_mul_eq_one_right D.v_mul_v]
      _ = D.v := by
            rw [mem_centralizer_singleton_iff.mp (mem_inf.mp D.w_mem_T).2, mul_inv_cancel_right]
  have h_ab_q : Commute (q ⟨D.a, Subgroup.subset_closure (by simp)⟩)
      (q ⟨D.b, Subgroup.subset_closure (by simp)⟩) :=
    (show Commute (⟨D.a, Subgroup.subset_closure (by simp)⟩ : ↥D.M)
        ⟨D.b, Subgroup.subset_closure (by simp)⟩ from Subtype.ext D.commute_a_b.eq).map q
  have h_aw_q : Commute (q ⟨D.a, Subgroup.subset_closure (by simp)⟩)
      (q ⟨D.w, Subgroup.subset_closure (by simp)⟩) := by
    show q ⟨D.a, Subgroup.subset_closure (by simp)⟩ * q ⟨D.w, Subgroup.subset_closure (by simp)⟩ =
      q ⟨D.w, Subgroup.subset_closure (by simp)⟩ * q ⟨D.a, Subgroup.subset_closure (by simp)⟩
    rw [← map_mul, ← map_mul]
    refine (QuotientGroup.mk'_eq_mk' N).mpr
      ⟨⟨D.v, D.v_mem_M⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers D.v), ?_⟩
    exact Subtype.ext hz_aw
  have h_bw_q : Commute (q ⟨D.b, Subgroup.subset_closure (by simp)⟩)
      (q ⟨D.w, Subgroup.subset_closure (by simp)⟩) := by
    show q ⟨D.b, Subgroup.subset_closure (by simp)⟩ * q ⟨D.w, Subgroup.subset_closure (by simp)⟩ =
      q ⟨D.w, Subgroup.subset_closure (by simp)⟩ * q ⟨D.b, Subgroup.subset_closure (by simp)⟩
    rw [← map_mul, ← map_mul]
    refine (QuotientGroup.mk'_eq_mk' N).mpr
      ⟨⟨D.v, D.v_mem_M⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers D.v), ?_⟩
    exact Subtype.ext hz_bw
  have hpair : S.Pairwise Commute := by
    intro x hx y hy _
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact Commute.refl _
    · exact h_ab_q
    · exact h_aw_q
    · exact h_ab_q.symm
    · exact Commute.refl _
    · exact h_bw_q
    · exact h_aw_q.symm
    · exact h_bw_q.symm
    · exact Commute.refl _
  have hS_top : closure S = ⊤ := by
    have h1 : closure (q '' gens) = ⊤ := by
      rw [← MonoidHom.map_closure, hgens,
        Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    have h2 : q '' gens = S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl <;> simp [S]
      · intro hy
        simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact ⟨⟨D.a, Subgroup.subset_closure (by simp)⟩, by simp [gens], rfl⟩
        · exact ⟨⟨D.b, Subgroup.subset_closure (by simp)⟩, by simp [gens], rfl⟩
        · exact ⟨⟨D.w, Subgroup.subset_closure (by simp)⟩, by simp [gens], rfl⟩
    simpa [h2] using h1
  have hQ : IsMulCommutative Q := by
    haveI : IsMulCommutative (⊤ : Subgroup Q) := by
      rw [← hS_top]
      exact Subgroup.isMulCommutative_closure hpair
    refine IsMulCommutative.of_comm fun x y => ?_
    have h : (Subgroup.topEquiv.symm x) * (Subgroup.topEquiv.symm y) =
        (Subgroup.topEquiv.symm y) * (Subgroup.topEquiv.symm x) := mul_comm' _ _
    simpa using congrArg Subgroup.topEquiv h
  have hcomm : commutator ↥D.M ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp hQ
  have hle : ⁅D.M, D.M⁆ ≤ H := by
    calc ⁅D.M, D.M⁆ = (commutator ↥D.M).map D.M.subtype :=
          (Subgroup.map_subtype_commutator D.M).symm
      _ ≤ N.map D.M.subtype := Subgroup.map_mono hcomm
      _ = H := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH_le_M]
  have hH_le : H ≤ ⁅D.M, D.M⁆ := by
    rw [Subgroup.zpowers_le]
    rw [show D.v = ⁅D.a, D.w⁆ from h_aw.symm]
    exact commutator_mem_commutator (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  exact le_antisymm hle hH_le

end CFSG.OddTranspositions.PartThree.Wong.SplitData
