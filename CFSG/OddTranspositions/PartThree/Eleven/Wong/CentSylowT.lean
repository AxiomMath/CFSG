module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDerived
import CFSG.RankThree.Co2.JFusion

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem second_centralizer_sylow_presentation :
    D.T = closure {D.a, D.b, D.w, D.r} ∧ Nat.card D.T = 32 ∧
    D.a ^ 2 = D.u * D.v ∧ D.b ^ 2 = D.u * D.v ∧ D.a * D.b = D.v ∧ Commute D.a D.b ∧
    D.w ^ 2 = 1 ∧ D.r ^ 2 = 1 ∧ Commute D.w D.r ∧
    D.w⁻¹ * D.a * D.w = D.b⁻¹ ∧ D.w⁻¹ * D.b * D.w = D.a⁻¹ ∧
    D.r⁻¹ * D.a * D.r = D.b ∧ D.r⁻¹ * D.b * D.r = D.a ∧
    ∃ P : Sylow 2 D.X, (P : Subgroup D.X).map D.X.subtype = D.T := by
  refine ⟨D.T_eq_closure, D.card_T, D.a_sq, D.b_sq, D.a_mul_b, D.commute_a_b, D.w_sq,
    D.r_sq, D.commute_w_r, D.conj_w_a_and_b.1, D.conj_w_a_and_b.2, D.conj_r_a_and_b.1,
    D.conj_r_a_and_b.2, ?_⟩
  have hT : IsPGroup 2 (D.T.subgroupOf D.X) := by
    have h0 : IsPGroup 2 ↥D.T :=
      IsPGroup.of_card (n := 5) (by rw [D.card_T]; norm_num)
    exact h0.of_equiv (Subgroup.subgroupOfEquivOfLe D.T_le_X).symm
  have hN : Subgroup.normalizer (D.T.subgroupOf D.X : Set ↥D.X) ≤ D.T.subgroupOf D.X := by
    intro g hgN
    rw [Subgroup.mem_subgroupOf]
    have hg_norm_T : ∀ t ∈ D.T, (g : G) * t * (g : G)⁻¹ ∈ D.T := by
      intro t ht
      have htX : t ∈ D.X := D.T_le_X ht
      have hmem : (⟨t, htX⟩ : ↥D.X) ∈ D.T.subgroupOf D.X := Subgroup.mem_subgroupOf.mpr ht
      have h := (Subgroup.mem_normalizer_iff.mp hgN ⟨t, htX⟩).mp hmem
      exact Subgroup.mem_subgroupOf.mp h
    have h_aw : ⁅D.a, D.w⁆ = D.v := by
      have haw : D.a * D.w = D.w * D.b⁻¹ := by rw [← D.conj_w_a_and_b.1]; group
      calc ⁅D.a, D.w⁆ = D.a * D.w * D.a⁻¹ * D.w⁻¹ := by rw [commutatorElement_def]
        _ = D.w * D.b⁻¹ * D.a⁻¹ * D.w⁻¹ := by rw [haw]
        _ = D.w * (D.b⁻¹ * D.a⁻¹) * D.w⁻¹ := by group
        _ = D.w * D.v * D.w⁻¹ := by
              rw [← mul_inv_rev, D.a_mul_b, inv_eq_of_mul_eq_one_right D.v_mul_v]
        _ = D.v := by
              rw [mem_centralizer_singleton_iff.mp (mem_inf.mp D.w_mem_T).2,
                mul_inv_cancel_right]
    have hgv_conj : (g : G) * D.v * (g : G)⁻¹ =
        ⁅(g : G) * D.a * (g : G)⁻¹, (g : G) * D.w * (g : G)⁻¹⁆ := by
      rw [← h_aw, conjugate_commutatorElement]
    have hTT : closure {D.u, D.v} = ⁅D.T, D.T⁆ :=
      D.commutator_T_eq.symm.trans (Subgroup.map_subtype_commutator D.T)
    have hgv_mem : (g : G) * D.v * (g : G)⁻¹ ∈ closure {D.u, D.v} := by
      rw [hTT, hgv_conj]
      exact commutator_mem_commutator (hg_norm_T D.a D.a_mem_T) (hg_norm_T D.w D.w_mem_T)
    have hgu_conj : (g : G)⁻¹ * D.u * (g : G) = D.u := by
      have h := mem_centralizer_singleton_iff.mp (g.2 : (g : G) ∈ centralizer {D.u})
      calc (g : G)⁻¹ * D.u * (g : G) = (g : G)⁻¹ * (D.u * (g : G)) := by group
        _ = (g : G)⁻¹ * ((g : G) * D.u) := by rw [← h]
        _ = D.u := by group
    obtain h1 | h1 | h1 | h1 := mem_closure_pair D.orderOf_u D.orderOf_v D.commute_u_v hgv_mem
    · exfalso
      have hv1 : D.v = 1 := by
        have h := congrArg (fun x => (g : G)⁻¹ * x * (g : G)) h1
        calc D.v = (g : G)⁻¹ * ((g : G) * D.v * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [h]; group
      have h2 := D.orderOf_v
      rw [hv1, orderOf_one] at h2
      norm_num at h2
    · exfalso
      apply D.v_ne_u
      have h := congrArg (fun x => (g : G)⁻¹ * x * (g : G)) h1
      calc D.v = (g : G)⁻¹ * ((g : G) * D.v * (g : G)⁻¹) * (g : G) := by group
        _ = (g : G)⁻¹ * D.u * (g : G) := by rw [h]
        _ = D.u := hgu_conj
    · have hcomm : (g : G) * D.v = D.v * (g : G) := (mul_inv_eq_iff_eq_mul).mp h1
      change (g : G) ∈ centralizer {D.u} ⊓ centralizer {D.v}
      exact mem_inf.mpr ⟨g.2, mem_centralizer_singleton_iff.mpr hcomm⟩
    · exfalso
      have hconjv : IsConj D.v (D.u * D.v) := isConj_iff.mpr ⟨(g : G), h1⟩
      have hu_uv : IsConj D.u (D.u * D.v) := D.isConj_u_v.trans hconjv
      have ht_uv : IsConj D.t (D.u * D.v) :=
        isConj_iff.mpr ⟨D.z⁻¹, by rw [inv_inv]; exact D.z_t⟩
      exact D.not_isConj_t_u (ht_uv.trans hu_uv.symm)
  obtain ⟨P, hP⟩ := CFSG.RankThree.Co2.exists_sylow_eq_of_normalizer_le (C := ↥D.X) (p := 2)
    (T := D.T.subgroupOf D.X) hT hN
  exact ⟨P, by rw [hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr D.T_le_X]⟩

end CFSG.OddTranspositions.PartThree.Wong.SplitData
