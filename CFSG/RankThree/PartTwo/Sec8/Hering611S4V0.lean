module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Reg
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Gen

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.KFacts.K426
open scoped commutatorElement

variable {Rg : ℕ → Gp}

theorem commute_of_prod {i j : ℕ} (h : prodG Rg [i, j] = prodG Rg [j, i]) :
    Commute (Rg i) (Rg j) := by
  simpa [prodG, Commute, SemiconjBy] using h

theorem inv_of_prod {a b : ℕ} (h : prodG Rg [a, b] = prodG Rg []) : Rg b = (Rg a)⁻¹ := by
  simp only [prodG_cons, prodG_nil, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

abbrev V0 (Rg : ℕ → Gp) : Subgroup Gp := Ksub Rg gens_V

abbrev M0 (Rg : ℕ → Gp) : Subgroup Gp := Ksub Rg gens_M

abbrev H0 (Rg : ℕ → Gp) : Subgroup Gp := Ksub Rg gens_H

theorem forall_image_list {α β : Type _} (f : α → β) (l : List α) (p : β → Prop) :
    (∀ s ∈ f '' {r | r ∈ l}, p s) ↔ ∀ r ∈ l, p (f r) := by
  simp only [Set.forall_mem_image, Set.mem_setOf_eq]

theorem forall_gens_V (p : Gp → Prop) :
    (∀ s ∈ Rg '' {r | r ∈ gens_V}, p s) ↔
      p (Rg r_v1) ∧ p (Rg r_v2) ∧ p (Rg r_v3) ∧ p (Rg r_v4) := by
  rw [forall_image_list]
  simp [gens_V]

theorem pow_of_ord {r m : ℕ} (h : orderOf (Rg r) = m) : Rg r ^ m = 1 := by
  have := pow_orderOf_eq_one (Rg r)
  rwa [h] at this

theorem V0_le (hR : Reg Rg) : V0 Rg ≤ j3P := by
  refine Ksub_le fun r hr => ?_
  simp only [gens_V, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using hR.v1_P
  · simpa using hR.v2_P
  · simpa using hR.v3_P
  · simpa using hR.v4_P

theorem V0_elem (hR : Reg Rg) : CFSG.Open.IsElemAbelian 2 (V0 Rg) := by
  have hcomm : ∀ i ∈ gens_V, ∀ j ∈ gens_V, Commute (Rg i) (Rg j) := by
    intro i hi j hj
    simp only [gens_V, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | exact commute_of_prod hR.comm_v1_v2
      | exact (commute_of_prod hR.comm_v1_v2).symm
      | exact commute_of_prod hR.comm_v1_v3
      | exact (commute_of_prod hR.comm_v1_v3).symm
      | exact commute_of_prod hR.comm_v1_v4
      | exact (commute_of_prod hR.comm_v1_v4).symm
      | exact commute_of_prod hR.comm_v2_v3
      | exact (commute_of_prod hR.comm_v2_v3).symm
      | exact commute_of_prod hR.comm_v2_v4
      | exact (commute_of_prod hR.comm_v2_v4).symm
      | exact commute_of_prod hR.comm_v3_v4
      | exact (commute_of_prod hR.comm_v3_v4).symm
  refine isElemAbelian_closure (S := Rg '' {r | r ∈ gens_V}) ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ _
    exact hcomm i hi j hj
  · rintro _ ⟨i, hi, rfl⟩
    simp only [gens_V, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    exacts [pow_of_ord hR.ord_v1, pow_of_ord hR.ord_v2, pow_of_ord hR.ord_v3,
      pow_of_ord hR.ord_v4]

theorem t1_mem (hR : Reg Rg) : Rg r_t1 ∈ V0 Rg := by simpa using hR.t1_V

theorem t1_ne (hR : Reg Rg) : Rg r_t1 ≠ 1 := by
  intro h
  have := hR.ord_t1
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem C_eq
    (hR : Reg Rg) :
    Ksub Rg gens_C = j3P ⊓ centralizer {Rg r_t1} := by
  obtain ⟨-, -, -, -, -, -, -, -, hrows, -⟩ := j3_centData
  have hlen : j3Rows.length = 2 := rfl
  have h0 : 0 < j3Rows.length := by rw [hlen]; norm_num
  obtain ⟨-, -, -, hcl, -⟩ := hrows (j3Rows[0]'h0) (List.getElem_mem h0)
  have hrow : (j3Rows[0]'h0).centGens = [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13,
      j3CentTbl 14] := by simp only [j3Rows, List.getElem_cons_zero]
  have hrep : (j3Rows[0]'h0).rep = j3CentTbl 9 := by simp only [j3Rows, List.getElem_cons_zero]
  rw [hrow, hrep] at hcl
  have e1 : {r | r ∈ gens_C} = ({r_c0, r_c1, r_c2, r_c3, r_c4} : Set ℕ) := by
    ext r
    simp [gens_C]
  have e2 : {x | x ∈ ([j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13,
      j3CentTbl 14] : List Table).toArray} =
        ({j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14} : Set Table) := by
    ext x
    simp
  rw [e2] at hcl
  rw [Ksub, e1, hR.init_t1, ← hcl]
  simp [Set.image_insert_eq, hR.init_c0, hR.init_c1, hR.init_c2, hR.init_c3, hR.init_c4]

theorem M0_le_P (hR : Reg Rg) : M0 Rg ≤ j3P := by
  refine Ksub_le fun r hr => ?_
  simp only [gens_M, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simpa using hR.m1_P
  · simpa using hR.m2_P

theorem mem_normalizer_V0 {m mi : ℕ} (hmi : Rg mi = (Rg m)⁻¹)
    (h : ∀ k ∈ gens_V, prodG Rg [m, k, mi] ∈ V0 Rg) : Rg m ∈ normalizer (V0 Rg : Set Gp) := by
  refine mem_normalizer_of_conj_gens (S := Rg '' {r | r ∈ gens_V}) rfl ?_
  rintro _ ⟨k, hk, rfl⟩
  have e : Rg m * Rg k * (Rg m)⁻¹ = prodG Rg [m, k, mi] := by simp [prodG, hmi, mul_assoc]
  rw [e]
  exact h k hk

theorem M0_le_N (hR : Reg Rg) : M0 Rg ≤ normalizer (V0 Rg : Set Gp) := by
  refine Ksub_le fun r hr => ?_
  simp only [gens_M, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine mem_normalizer_V0 (inv_of_prod hR.m1_inv) fun k hk => ?_
    simp only [gens_V, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    exacts [hR.m1_V1, hR.m1_V2, hR.m1_V3, hR.m1_V4]
  · refine mem_normalizer_V0 (inv_of_prod hR.m2_inv) fun k hk => ?_
    simp only [gens_V, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    exacts [hR.m2_V1, hR.m2_V2, hR.m2_V3, hR.m2_V4]

theorem normalizer_V0
    (hR : Reg Rg) :
    normalizer (V0 Rg : Set Gp) ⊓ j3P = M0 Rg := by
  refine normalizer_inf_eq (P := j3P) (C := Ksub Rg gens_C) (t := Rg r_t1)
    (S := Rg '' {r | r ∈ gens_V}) rfl hR.card_V (t1_mem hR) (t1_ne hR) (M0_le_P hR)
    (M0_le_N hR) hR.card_M (C_eq hR) ?_
  have hset : {x | x ∈ Ksub Rg gens_C ∧ ∀ s ∈ Rg '' {r | r ∈ gens_V}, x * s * x⁻¹ ∈ V0 Rg} =
      {x | x ∈ Ksub Rg gens_C ∧ (x * Rg r_v1 * x⁻¹ ∈ Ksub Rg gens_V ∧
        (x * Rg r_v2 * x⁻¹ ∈ Ksub Rg gens_V ∧ (x * Rg r_v3 * x⁻¹ ∈ Ksub Rg gens_V ∧
          x * Rg r_v4 * x⁻¹ ∈ Ksub Rg gens_V)))} := by
    ext x
    simp only [Set.mem_setOf_eq, forall_gens_V]
  rw [hset, hR.loop_N]

theorem H0_le_M0 (hR : Reg Rg) : H0 Rg ≤ M0 Rg := by
  refine Ksub_le fun r hr => ?_
  simp only [gens_H, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using hR.h1_M
  · simpa using hR.h2_M
  · simpa using hR.h3_M
  · simpa using hR.h4_M

theorem H0_perfect (hR : Reg Rg) : ⁅H0 Rg, H0 Rg⁆ = H0 Rg := by
  have hcomm : ∀ {p q pi qi k : ℕ}, prodG Rg [p, pi] = prodG Rg [] →
      prodG Rg [q, qi] = prodG Rg [] → prodG Rg [k] = prodG Rg [p, q, pi, qi] →
      Rg k = ⁅Rg p, Rg q⁆ := by
    intro p q pi qi k hp hq hk
    have e1 := inv_of_prod hp
    have e2 := inv_of_prod hq
    simp only [prodG_cons, prodG_nil, mul_one] at hk
    rw [hk, e1, e2, commutatorElement_def]
    group
  have hKc : Ksub Rg gens_K ≤ ⁅H0 Rg, H0 Rg⁆ := by
    refine Ksub_le fun r hr => ?_
    simp only [gens_K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hcomm hR.p1_inv hR.q1_inv hR.k1_def]
      exact commutator_mem_commutator (by simpa using hR.p1_H) (by simpa using hR.q1_H)
    · rw [hcomm hR.p2_inv hR.q2_inv hR.k2_def]
      exact commutator_mem_commutator (by simpa using hR.p2_H) (by simpa using hR.q2_H)
  have hKH : Ksub Rg gens_K ≤ H0 Rg := by
    refine Ksub_le fun r hr => ?_
    simp only [gens_K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hR.k1_H
    · simpa using hR.k2_H
  have hKeq : Ksub Rg gens_K = H0 Rg :=
    eq_of_le_of_card_ge hKH (by rw [hR.card_K, hR.card_H])
  refine le_antisymm (commutator_le.mpr fun a ha b hb => ?_) (hKeq ▸ hKc)
  rw [commutatorElement_def]
  exact (H0 Rg).mul_mem ((H0 Rg).mul_mem ((H0 Rg).mul_mem ha hb) ((H0 Rg).inv_mem ha))
    ((H0 Rg).inv_mem hb)

theorem M0_residual (hR : Reg Rg) : inSubgroup perfectResidual (M0 Rg) = H0 Rg := by
  refine inSubgroup_perfectResidual_eq (S := Rg '' {r | r ∈ gens_H}) (H0_le_M0 hR) rfl
    (H0_perfect hR) ?_ (by rw [hR.card_M, hR.card_H])
  intro x hx s hs
  obtain ⟨h1, h2, h3, h4⟩ := hR.loop_H x hx
  obtain ⟨k, hk, rfl⟩ := hs
  simp only [gens_H, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
