
module

public import CFSG.Sporadic.Fi24.SetupBase
public import CFSG.Sporadic.Fi24.VerifySpec

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure Sub781 where
  sp : Submodule (ZMod 3) (Fin 781 → ZMod 3)

theorem Sub781.ext' {S T : Sub781} (h : S.sp = T.sp) : S = T := by
  cases S; cases T; simp only at h; rw [h]

theorem vecW_frApply {Y : Array W} (hY : RowsWF Y) (hYs : Y.size = 781) {x : W}
    (hx : x.wf = true) :
    vecW (frApply (frTable Y) x) = Matrix.mulVec (matW 781 781 Y).transpose (vecW x) := by
  funext c
  unfold vecW
  rw [(frApply_spec hY hx c.val).2, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_range_add_sum_Ico _ (show 781 ≤ 784 by norm_num),
    show ∑ j ∈ Finset.Ico 781 784, x.val j * (rowW Y j).val c.val = 0 from
      Finset.sum_eq_zero fun j hj => by
        rw [rowW_ge (X := Y) (by rw [Finset.mem_Ico] at hj; omega), W.val_zero, mul_zero],
    add_zero, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.transpose_apply, matW_apply, mul_comm]

theorem rowSpan_stepForm {Y : Array W} (hY : RowsWF Y) (hYs : Y.size = 781) {X : Array W}
    (hX : RowsWF X) (hXs : X.size = 253) :
    rowSpan 253 (stepForm (frTable Y) X).rows =
      (rowSpan 253 X).map (Matrix.mulVecLin (matW 781 781 Y).transpose) := by
  unfold stepForm
  have hXw : RowsWF (X.map (frApply (frTable Y))) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    rw [Array.getElem_map]
    exact (frApply_spec hY (hX _ (Array.getElem_mem _)) 0).1
  have hs : (X.map (frApply (frTable Y))).size = 253 := by rw [Array.size_map, hXs]
  obtain ⟨-, -, h3⟩ := rref_spec 781 hXw
  rw [hs] at h3
  rw [h3]
  unfold rowSpan
  rw [Submodule.map_span, ← Set.range_comp]
  have hfun : (fun i : Fin 253 => vecW (rowW (X.map (frApply (frTable Y))) i.val)) =
      (Matrix.mulVecLin (matW 781 781 Y).transpose) ∘ (fun i : Fin 253 => vecW (rowW X i.val)) := by
    funext i
    simp only [Function.comp_apply, Matrix.mulVecLin_apply]
    rw [rowW_map _ X (frApply_zero _), vecW_frApply hY hYs (hX.row i.val)]
  rw [hfun]

theorem gensT_get_one : (gensT ()).get 1 = frTable matAT := by
  unfold Gens.get
  rw [ite_eq_left rfl]
  simp only [gensT]

theorem gensT_get_two : (gensT ()).get 2 = frTable matBT := by
  unfold Gens.get
  rw [ite_eq_right (by decide)]
  simp only [gensT]

theorem matW_matAT_T : (matW 781 781 matAT).transpose = mA := by
  rw [matW_matAT, Matrix.transpose_transpose]

theorem matW_matBT_T : (matW 781 781 matBT).transpose = mB := by
  rw [matW_matBT, Matrix.transpose_transpose]

theorem stepForm_facts {Y : Array W} (hY : RowsWF Y) {X : Array W} (hX : RowsWF X) :
    (stepForm (frTable Y) X).rows.size = X.size ∧ RowsWF (stepForm (frTable Y) X).rows := by
  unfold stepForm
  have hXw : RowsWF (X.map (frApply (frTable Y))) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    rw [Array.getElem_map]
    exact (frApply_spec hY (hX _ (Array.getElem_mem _)) 0).1
  obtain ⟨h1, h2, -⟩ := rref_spec 781 hXw
  rw [Array.size_map] at h1
  exact ⟨h1, h2⟩

theorem gensT_get (l : ℕ) : (gensT ()).get l = frTable matAT ∨ (gensT ()).get l = frTable matBT := by
  unfold Gens.get
  by_cases h : l = 1
  · rw [if_pos h]
    left
    simp only [gensT]
  · rw [if_neg h]
    right
    simp only [gensT]

theorem rootForm_facts' : (rootForm ()).rows.size = 253 ∧ RowsWF (rootForm ()).rows := by
  have hw : RowsWF (initRows ()) := by
    intro x hx
    unfold initRows at hx
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
    exact ofTrits_wf (by norm_num) _
  have hs : (initRows ()).size = 253 := by unfold initRows; simp
  obtain ⟨h1, h2, -⟩ := rref_spec 781 hw
  exact ⟨h1.trans hs, h2⟩

theorem formAt_facts (E : Enum) (k : ℕ) :
    (formAt gensT E rootForm k).rows.size = 253 ∧ RowsWF (formAt gensT E rootForm k).rows := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : 0 < k ∧ ap E.par k < k
    · rw [formAt_pos _ _ _ h.1 h.2]
      obtain ⟨hs, hw⟩ := ih _ h.2
      rcases gensT_get (ap E.lab k) with e | e <;> rw [e]
      · obtain ⟨h1, h2⟩ := stepForm_facts rowsWF_matAT hw
        exact ⟨h1.trans hs, h2⟩
      · obtain ⟨h1, h2⟩ := stepForm_facts rowsWF_matBT hw
        exact ⟨h1.trans hs, h2⟩
    · rw [formAt, dif_neg h]
      exact rootForm_facts'

noncomputable abbrev form (k : ℕ) : RRef := formAt gensT orb rootForm k

@[expose] noncomputable def pt (k : ℕ) : Sub781 := ⟨rowSpan 253 (form k).rows⟩

theorem pt_sp (k : ℕ) : (pt k).sp = ptSub k := rfl

theorem form_facts {k : ℕ} (_hk : k < nPts) :
    (form k).rows.size = 253 ∧ RowsWF (form k).rows := formAt_facts orb k

theorem nPts_eq : nPts = 306936 := rfl

end CFSG.Sporadic.Fi24
