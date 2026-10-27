module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8)

@[expose] def pa : P8 := swap 3 4 * swap 5 6
@[expose] def pb : P8 := swap 3 5 * swap 4 6
@[expose] def pc : P8 := swap 0 1 * swap 2 7
@[expose] def pd : P8 := swap 0 2 * swap 1 7

@[expose] def qa : P8 := swap 3 4 * swap 5 7
@[expose] def qb : P8 := swap 3 5 * swap 4 7
@[expose] def qc : P8 := swap 0 1 * swap 2 6
@[expose] def qd : P8 := swap 0 2 * swap 1 6

@[expose] def tup4 (a b c d : P8) (t : Fin 2 × Fin 2 × Fin 2 × Fin 2) : P8 :=
  a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2.1 : ℕ) * d ^ (t.2.2.2 : ℕ)

theorem mem_closure_four_iff {a b c d : P8}
    (hmul : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2, ∃ r,
      tup4 a b c d t * tup4 a b c d s = tup4 a b c d r)
    (hinv : ∀ t, (tup4 a b c d t)⁻¹ = tup4 a b c d t) (x : P8) :
    x ∈ Subgroup.closure ({a, b, c, d} : Set P8) ↔ ∃ t, x = tup4 a b c d t := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨(1, 0, 0, 0), by simp [tup4]⟩
      · exact ⟨(0, 1, 0, 0), by simp [tup4]⟩
      · exact ⟨(0, 0, 1, 0), by simp [tup4]⟩
      · exact ⟨(0, 0, 0, 1), by simp [tup4]⟩
    | one => exact ⟨(0, 0, 0, 0), by simp [tup4]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t, rfl⟩ := hx
      obtain ⟨s, rfl⟩ := hy
      obtain ⟨r, hr⟩ := hmul t s
      exact ⟨r, hr⟩
    | inv x _ hx =>
      obtain ⟨t, rfl⟩ := hx
      exact ⟨t, hinv t⟩
  · rintro ⟨t, rfl⟩
    have ha : a ∈ Subgroup.closure ({a, b, c, d} : Set P8) := subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({a, b, c, d} : Set P8) := subset_closure (by simp)
    have hc : c ∈ Subgroup.closure ({a, b, c, d} : Set P8) := subset_closure (by simp)
    have hd : d ∈ Subgroup.closure ({a, b, c, d} : Set P8) := subset_closure (by simp)
    unfold tup4
    exact mul_mem (mul_mem (mul_mem (pow_mem ha _) (pow_mem hb _)) (pow_mem hc _)) (pow_mem hd _)

theorem Ua_eq_closure : Ua = Subgroup.closure ({pa, pb, pc, pd} : Set P8) := by
  unfold Ua v4 pa pb pc pd
  rw [← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem Ub_eq_closure : Ub = Subgroup.closure ({qa, qb, qc, qd} : Set P8) := by
  unfold Ub v4 qa qb qc qd
  rw [← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem tupU_mul : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2, ∃ r,
    tup4 pa pb pc pd t * tup4 pa pb pc pd s = tup4 pa pb pc pd r := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem tupU_inv : ∀ t, (tup4 pa pb pc pd t)⁻¹ = tup4 pa pb pc pd t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem tupV_mul : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2, ∃ r,
    tup4 qa qb qc qd t * tup4 qa qb qc qd s = tup4 qa qb qc qd r := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem tupV_inv : ∀ t, (tup4 qa qb qc qd t)⁻¹ = tup4 qa qb qc qd t := by
  decide +kernel

theorem mem_Ua_iff (x : P8) : x ∈ Ua ↔ ∃ t, x = tup4 pa pb pc pd t := by
  rw [Ua_eq_closure]
  exact mem_closure_four_iff tupU_mul tupU_inv x

theorem mem_Ub_iff (x : P8) : x ∈ Ub ↔ ∃ t, x = tup4 qa qb qc qd t := by
  rw [Ub_eq_closure]
  exact mem_closure_four_iff tupV_mul tupV_inv x

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
