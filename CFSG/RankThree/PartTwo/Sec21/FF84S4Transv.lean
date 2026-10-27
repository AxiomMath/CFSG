module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4UFacts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

theorem pa_memU : pa ∈ Ua := by
  rw [Ua_eq_closure]; exact Subgroup.subset_closure (by simp)
theorem qa_memU : qa ∈ Ub := by
  rw [Ub_eq_closure]; exact Subgroup.subset_closure (by simp)

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem transv_dec_Ua : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 pa pb pc pd t ≠ 1 →
    (tup4 pa pb pc pd t * cc = cc * tup4 pa pb pc pd t ∨
      (∃ s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        tup4 pa pb pc pd s * cc⁻¹ * (tup4 pa pb pc pd s)⁻¹ * cc⁻¹⁻¹ = tup4 pa pb pc pd t) ∨
      (∃ g ∈ ([swap 1 3 * swap 2 6, swap 2 3 * swap 4 7, swap 1 3 * swap 5 7,
          swap 1 3 * swap 2 4, swap 1 3 * swap 2 5, swap 1 3 * swap 6 7, swap 1 3 * swap 4 7,
          swap 2 3 * swap 5 7, swap 2 3 * swap 6 7] : List P8),
        g * tup4 pa pb pc pd t = tup4 pa pb pc pd t * g ∧ Equiv.Perm.sign g = 1 ∧
          ∀ s, g * pa * g⁻¹ ≠ tup4 pa pb pc pd s)) := by
  decide +kernel

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem transv_dec_Ub : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 qa qb qc qd t ≠ 1 →
    (tup4 qa qb qc qd t * cc = cc * tup4 qa qb qc qd t ∨
      (∃ s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        tup4 qa qb qc qd s * cc⁻¹ * (tup4 qa qb qc qd s)⁻¹ * cc⁻¹⁻¹ = tup4 qa qb qc qd t) ∨
      (∃ g ∈ ([swap 2 3 * swap 4 6, swap 1 3 * swap 5 6, swap 1 3 * swap 2 4,
          swap 1 3 * swap 6 7, swap 1 3 * swap 4 6, swap 1 3 * swap 2 5, swap 1 3 * swap 2 7,
          swap 2 3 * swap 6 7, swap 2 3 * swap 5 6] : List P8),
        g * tup4 qa qb qc qd t = tup4 qa qb qc qd t * g ∧ Equiv.Perm.sign g = 1 ∧
          ∀ s, g * qa * g⁻¹ ≠ tup4 qa qb qc qd s)) := by
  decide +kernel

theorem A_transv_Ua : ∀ x ∈ Ua, x ≠ 1 → x ∉ ⁅Ua, Subgroup.zpowers cc⁆ → x ∉ Ua ⊓ Cen cc →
    ¬ (Cen x ⊓ A8s ≤ Nor Ua) := by
  intro x hx hne h1 h2
  obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 hx
  rcases transv_dec_Ua t hne with hC | ⟨s, hs⟩ | ⟨g, -, hcomm, hsign, hnot⟩
  · exact absurd (Subgroup.mem_inf.2 ⟨(mem_Ua_iff _).2 ⟨t, rfl⟩, mem_centralizer_singleton_iff.2 hC⟩)
      h2
  · have hmem : tup4 pa pb pc pd t ∈ ⁅Ua, Subgroup.zpowers cc⁆ := by
      have := commutator_mem_commutator ((mem_Ua_iff _).2 ⟨s, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers cc))
      rw [commutatorElement_def, hs] at this
      exact this
    exact absurd hmem h1
  · intro hle
    have hgN : g ∈ Nor Ua := hle ⟨mem_centralizer_singleton_iff.2 hcomm, mem_alternatingGroup.2 hsign⟩
    have hgp : g * pa * g⁻¹ ∈ Ua := (Subgroup.mem_normalizer_iff.1 hgN pa).1 pa_memU
    obtain ⟨s, hs⟩ := (mem_Ua_iff _).1 hgp
    exact hnot s hs

theorem A_transv_Ub : ∀ x ∈ Ub, x ≠ 1 → x ∉ ⁅Ub, Subgroup.zpowers cc⁆ → x ∉ Ub ⊓ Cen cc →
    ¬ (Cen x ⊓ A8s ≤ Nor Ub) := by
  intro x hx hne h1 h2
  obtain ⟨t, rfl⟩ := (mem_Ub_iff x).1 hx
  rcases transv_dec_Ub t hne with hC | ⟨s, hs⟩ | ⟨g, -, hcomm, hsign, hnot⟩
  · exact absurd (Subgroup.mem_inf.2 ⟨(mem_Ub_iff _).2 ⟨t, rfl⟩, mem_centralizer_singleton_iff.2 hC⟩)
      h2
  · have hmem : tup4 qa qb qc qd t ∈ ⁅Ub, Subgroup.zpowers cc⁆ := by
      have := commutator_mem_commutator ((mem_Ub_iff _).2 ⟨s, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers cc))
      rw [commutatorElement_def, hs] at this
      exact this
    exact absurd hmem h1
  · intro hle
    have hgN : g ∈ Nor Ub := hle ⟨mem_centralizer_singleton_iff.2 hcomm, mem_alternatingGroup.2 hsign⟩
    have hgq : g * qa * g⁻¹ ∈ Ub := (Subgroup.mem_normalizer_iff.1 hgN qa).1 qa_memU
    obtain ⟨s, hs⟩ := (mem_Ub_iff _).1 hgq
    exact hnot s hs

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
