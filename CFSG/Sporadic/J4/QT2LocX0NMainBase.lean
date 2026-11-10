
module

public import CFSG.Sporadic.J4.QT2LocX0NCheck
public import CFSG.Sporadic.J4.QT2LocX0MainBase

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem x0GenRows_size : x0GenRows.size = 8 := by
  simp [x0GenRows, x0Words, x0Strings]

theorem x0AllRows_zero : x0AllRows[0]! = x0GenRows[0]! := by
  have hs : 0 < x0GenRows.size := by rw [x0GenRows_size]; norm_num
  rw [getElem!_pos x0AllRows 0 (by simp [x0AllRows, x0InvRows]; omega),
    getElem!_pos x0GenRows 0 hs]
  exact Array.getElem_append_left hs

theorem Mx_fiveElt
    (hM : MatFacts) : Mx fiveElt = rowsMatrix (x0GenRows[0]!) := by
  rw [← x0Gen_zero hM, Mx_x0Gen hM (by norm_num), x0AllRows_zero]

theorem x0Gens_zero_facts :
    wfRows (x0GenRows[0]!) = true ∧ wfRows (x0InvRows[0]!) = true ∧
    eqRows (mulRows (x0GenRows[0]!) (x0InvRows[0]!)) idRows = true ∧
    eqRows (mulRows (x0InvRows[0]!) (x0GenRows[0]!)) idRows = true := by
  have h := chkX0Gens_true
  unfold chkX0Gens at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩ := h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, -⟩ := h5 0 (by norm_num)
  exact ⟨a, b, c, d⟩

theorem x0GenRows_zero_wf :
    wfRows (x0GenRows[0]!) = true := x0Gens_zero_facts.1

theorem x0InvRows_zero_wf :
    wfRows (x0InvRows[0]!) = true := x0Gens_zero_facts.2.1

theorem wfRows_mulRows {M N : Array V2} (hM : wfRows M = true) (hN : wfRows N = true) :
    wfRows (mulRows M N) = true :=
  wfRows_of (by rw [mulRows_size]; exact wfRows_size hM) (mulRows_wf M (wfRows_mem hN))

theorem Mx_fiveElt_inv
    (hM : MatFacts) : Mx fiveElt⁻¹ = rowsMatrix (x0InvRows[0]!) := by
  have e1 : rowsMatrix (x0InvRows[0]!) * rowsMatrix (x0GenRows[0]!) = 1 := by
    rw [← rowsMatrix_mulRows, eqRows_iff.1 x0Gens_zero_facts.2.2.2, rowsMatrix_idRows]
  have e2 : Mx fiveElt * Mx fiveElt⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc Mx fiveElt⁻¹ = (rowsMatrix (x0InvRows[0]!) * rowsMatrix (x0GenRows[0]!)) * Mx fiveElt⁻¹ := by
        rw [e1, one_mul]
    _ = rowsMatrix (x0InvRows[0]!) * (Mx fiveElt * Mx fiveElt⁻¹) := by
        rw [mul_assoc, ← Mx_fiveElt hM]
    _ = rowsMatrix (x0InvRows[0]!) := by rw [e2, mul_one]

noncomputable def nElt : J := QT2A.el5 nWordU * eta uJ 11 nMask * QT2A.el5 nWordV

theorem Mx_nElt (hM : MatFacts) : Mx nElt = rowsMatrix nRows := by
  unfold nElt nRows
  rw [map_mul, map_mul, QT2A.Mx_el5 hM, Mx_eta hM 11 le_rfl, QT2A.Mx_el5 hM,
    ← rowsMatrix_mulRows, ← rowsMatrix_mulRows]
  rfl

theorem nElt_conj
    (hM : MatFacts) : nElt * fiveElt = fiveElt ^ 2 * nElt := by
  apply Mx_injective
  have h := eqRows_iff.1 chkNConj_true
  have h2 := congrArg rowsMatrix h
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, ← Mx_nElt hM,
    ← Mx_fiveElt hM] at h2
  rw [map_mul, map_mul, map_pow, h2, pow_two]

theorem exists_conj_fiveElt_sq
    (hM : MatFacts) : ∃ n : J, n * fiveElt * n⁻¹ = fiveElt ^ 2 := by
  refine ⟨nElt, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, nElt_conj hM]

end CFSG.Sporadic.J4.QT2
