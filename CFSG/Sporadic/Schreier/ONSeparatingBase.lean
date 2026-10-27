module

public import CFSG.Sporadic.Schreier.ONActions
public import CFSG.Sporadic.Schreier.ONPermArr

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

theorem formRows_size : (rowsOf 154 Data.formPayload).size = 154 := rowsOf_size _

theorem toMat_formRows : toMat 154 (rowsOf 154 Data.formPayload) = invariantForm :=
  toMat_rowsOf 154 _

theorem form_parts : invariantFormᵀ = invariantForm ∧
    toMat 154 (invV 154 (rowsOf 154 Data.formPayload)) * invariantForm = 1 ∧
    mAᵀ * invariantForm * mA = invariantForm ∧ mBᵀ * invariantForm * mB = invariantForm := by
  have h := vectorFacts.form
  unfold formOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, hs⟩, hw⟩, h2⟩, h3⟩, h4⟩ := h
  have hM := RowsWF.rowsOf 154 Data.formPayload
  have hT := fun X : Array V => RowsWF.transpose 154 X
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := toMat_eq_of_eqM h1
    rwa [toMat_transpose, toMat_formRows] at e
  · have e := toMat_eq_of_eqM h2
    rwa [toMat_mul hs (rowsWF_of_wfM hw) hM, toMat_idM, toMat_formRows] at e
  · have e := toMat_eq_of_eqM h3
    rw [toMat_mul (by simp [mul, F3.Native.transpose]) (RowsWF.mul _ 154 (hT _) hM)
      rowsWF_rowsA, toMat_mul (by simp [F3.Native.transpose]) (hT _) hM, toMat_transpose,
      toMat_rowsA, toMat_formRows] at e
    exact e
  · have e := toMat_eq_of_eqM h4
    rw [toMat_mul (by simp [mul, F3.Native.transpose]) (RowsWF.mul _ 154 (hT _) hM)
      rowsWF_rowsB, toMat_mul (by simp [F3.Native.transpose]) (hT _) hM,
      toMat_transpose, toMat_rowsB, toMat_formRows] at e
    exact e

theorem form_symm : invariantFormᵀ = invariantForm := form_parts.1

theorem form_det_ne_zero : invariantForm.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det form_parts.2.1
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem mat_transpose_form
    (g : J) : (mat g)ᵀ * invariantForm * mat g = invariantForm := by
  obtain ⟨g, hg⟩ := g
  show (g : Matrix (Fin 154) (Fin 154) (ZMod 3))ᵀ * invariantForm *
    (g : Matrix (Fin 154) (Fin 154) (ZMod 3)) = invariantForm
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact form_parts.2.2.1
    · exact form_parts.2.2.2
  | one => simp
  | mul x y _ _ hx hy =>
    calc
      ((x * y : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3))ᵀ *
            invariantForm *
            ((x * y : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3))
          = (y : Matrix (Fin 154) (Fin 154) (ZMod 3))ᵀ *
            ((x : Matrix (Fin 154) (Fin 154) (ZMod 3))ᵀ * invariantForm *
              (x : Matrix (Fin 154) (Fin 154) (ZMod 3))) *
            (y : Matrix (Fin 154) (Fin 154) (ZMod 3)) := by
        simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = invariantForm := by rw [hx, hy]
  | inv x _ hx =>
    have hxi : (x : Matrix (Fin 154) (Fin 154) (ZMod 3)) * ((x⁻¹ : GL (Fin 154) (ZMod 3)) :
        Matrix (Fin 154) (Fin 154) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    set xi : Matrix (Fin 154) (Fin 154) (ZMod 3) := ((x⁻¹ : GL (Fin 154) (ZMod 3)) :
      Matrix (Fin 154) (Fin 154) (ZMod 3)) with hxidef
    calc
      xiᵀ * invariantForm * xi
          = xiᵀ * ((x : Matrix (Fin 154) (Fin 154) (ZMod 3))ᵀ * invariantForm *
            (x : Matrix (Fin 154) (Fin 154) (ZMod 3))) * xi := by rw [hx]
      _ = ((x : Matrix (Fin 154) (Fin 154) (ZMod 3)) * xi)ᵀ * invariantForm *
            ((x : Matrix (Fin 154) (Fin 154) (ZMod 3)) * xi) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = invariantForm := by rw [hxi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem pairing_mulVec
    (g : J) (x y : Vec) :
    (mat g *ᵥ x) ⬝ᵥ (invariantForm *ᵥ (mat g *ᵥ y)) = x ⬝ᵥ (invariantForm *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, mat_transpose_form]

theorem pairing_invariant
    {g : Equiv.Perm (Fin N)} (hg : g ∈ Pv) (i j : Fin N) :
    pairing (g i) (g j) = pairing i j := by
  rw [← range_phiV] at hg
  obtain ⟨h, rfl⟩ := hg
  rw [pairing, pairing, vv_phiV, vv_phiV]
  exact pairing_mulVec h _ _

theorem pairing_symm (i j : ℕ) : pairing i j = pairing j i := by
  rw [pairing, pairing, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, form_symm,
    dotProduct_comm]

theorem matrix_entry_mul (C M : Matrix (Fin 154) (Fin 154) (ZMod 3)) (i j : Fin 154) :
    (Cᵀ * M * C) i j = (fun r => C r i) ⬝ᵥ (M *ᵥ fun s => C s j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

@[expose] def gramGraph : SimpleGraph (Fin 154) :=
  SimpleGraph.fromRel fun i j => pairing (spanIndex i) (spanIndex j) ≠ 0

theorem gramGraph_adj (i j : Fin 154) :
    gramGraph.Adj i j ↔ i ≠ j ∧ pairing (spanIndex i) (spanIndex j) ≠ 0 := by
  rw [gramGraph, SimpleGraph.fromRel_adj, pairing_symm (spanIndex j)]
  exact and_congr_right fun _ => or_self_iff

abbrev gramM : Array V := Native.gram vectorOrbit Data.spanIdx (rowsOf 154 Data.formPayload)

theorem toMat_gram : toMat 154 gramM =
    basisMatrixᵀ * invariantForm * basisMatrix := by
  unfold gramM Native.gram
  rw [toMat_mul (by simp [F3.Native.mul, toVM, spanRows, spanIdx_size])
      (RowsWF.mul _ 154 rowsWF_spanRows (RowsWF.rowsOf 154 _)) (RowsWF.transpose 154 _),
    toMat_mul (by simp [toVM, spanRows, spanIdx_size]) rowsWF_spanRows
      (RowsWF.rowsOf 154 _), toMat_transpose, toMat_spanRows, toMat_formRows,
    Matrix.transpose_transpose]

theorem zmod3_natCast_eq_zero {n : ℕ} (hn : n < 3) : ((n : ZMod 3) = 0) ↔ n = 0 := by
  interval_cases n <;> decide

theorem gram_entry_ne_zero {i j : Fin 154}
    (h : gramM[i.val]!.get j.val ≠ 0) :
    pairing (spanIndex i) (spanIndex j) ≠ 0 := by
  have e := congrFun (congrFun toMat_gram i) j
  rw [toMat_apply, matrix_entry_mul] at e
  have hcol : ∀ k : Fin 154, (fun r => basisMatrix r k) = vv (spanIndex k) := fun k => by
    funext r
    rfl
  rw [hcol, hcol] at e
  rw [pairing, ← e]
  intro h0
  apply h
  have hlt : (Native.gram vectorOrbit Data.spanIdx (rowsOf 154 Data.formPayload))[i.val]!.get j.val
      < 3 := by
    unfold V.get
    split_ifs <;> norm_num
  exact (zmod3_natCast_eq_zero hlt).1 h0

theorem gramGraph_connected : gramGraph.Connected := by
  have h := vectorFacts.gram
  set G := Native.gram vectorOrbit Data.spanIdx (rowsOf 154 Data.formPayload)
  set par := (gramTree G).1
  set dep := (gramTree G).2
  unfold gramConnOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hd0, hall⟩ := h
  have hstep : ∀ y < 154, y ≠ 0 → par[y]! < 154 ∧ par[y]! ≠ y ∧ G[par[y]!]!.get y ≠ 0 ∧
      dep[par[y]!]! < dep[y]! := by
    intro y hy hy0
    have := CFSG.ONSchreier.allBelowN_spec hall hy
    simp only [Bool.or_eq_true, beq_iff_eq, hy0, false_or, Bool.and_eq_true,
      decide_eq_true_eq, bne_iff_ne, ne_eq] at this
    exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2⟩
  have hreach : ∀ d, ∀ y : Fin 154, dep[y.val]! = d → gramGraph.Reachable 0 y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hy
      by_cases hy0 : y.val = 0
      · have : y = 0 := Fin.ext hy0
        rw [this]
      · obtain ⟨hp, hne, hG, hlt⟩ := hstep y.val y.isLt hy0
        have hr := ih _ (hy ▸ hlt) ⟨par[y.val]!, hp⟩ rfl
        refine hr.trans (SimpleGraph.Adj.reachable ?_)
        rw [gramGraph_adj]
        refine ⟨fun h => hne (congrArg Fin.val h), gram_entry_ne_zero hG⟩
  exact ⟨fun u v => (hreach _ u rfl).symm.trans (hreach _ v rfl)⟩

theorem baseList_length : Data.baseList.length = 29 := base_facts.1

theorem baseIndex_eq {k : ℕ} (hk : k < 29) :
    baseIndex k = Data.baseList[k]'(by rw [baseList_length]; exact hk) := by
  rw [baseIndex, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
  rfl

theorem baseIndex_lt {k : ℕ} (hk : k < 29) : baseIndex k < N := by
  rw [baseIndex_eq hk]
  exact base_facts.2.2 _ (List.getElem_mem _)

theorem baseList_getElem! {k : ℕ} (hk : k < 29) : Data.baseList[k]! = baseIndex k := by
  rw [baseIndex_eq hk, getElem!_pos Data.baseList k (by rw [baseList_length]; exact hk)]

theorem sigRows_size : (sigRows vectorOrbit (rowsOf 154 Data.formPayload) Data.baseList).size =
    154 := by simp [sigRows]

theorem toMat_sigRows (k j : Fin 154) :
    toMat 154 (sigRows vectorOrbit (rowsOf 154 Data.formPayload) Data.baseList) k j =
      if (k : ℕ) < 29 then (vv (baseIndex k) ᵥ* invariantForm) j else 0 := by
  rw [toMat_apply, sigRows, getElem!_pos _ k.val (by simp), Array.getElem_ofFn]
  simp only [baseList_length]
  split_ifs with hk
  · rw [V.val_comb 154 _ _ (RowsWF.rowsOf 154 _) (vkeys_wf (by
      rw [baseList_getElem! hk]; exact baseIndex_lt hk)), baseList_getElem! hk,
      Matrix.vecMul, dotProduct, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [vv_of_lt (baseIndex_lt hk), ← toMat_formRows, toMat_apply]
    rfl
  · exact V.val_zero _

theorem vecOf_sig {i : ℕ} (hi : i < N) (k : Fin 154) :
    vecOf (sigsOf vectorOrbit sigT)[i]! k =
      if (k : ℕ) < 29 then pairing (baseIndex k) i else 0 := by
  rw [sigsOf, getElem!_pos _ i (by simp; exact hi), Array.getElem_ofFn]
  simp only
  rw [vecOf_mulVecT _ (vkeys_wf hi), ← vv_of_lt hi, Matrix.mulVec, dotProduct]
  simp only [toMat_sigRows]
  split_ifs with hk
  · rw [pairing, Matrix.dotProduct_mulVec, dotProduct]
  · simp

theorem sig_parts :
    ∀ i < N, canon154 (sigsOf vectorOrbit sigT)[i]! = true ∧
    posOf (indexOf (sigsOf vectorOrbit sigT)) nPts (sigsOf vectorOrbit sigT)[i]! = i := by
  have h := vectorFacts.sig
  unfold sigOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  intro i hi
  have := (CFSG.Sporadic.Th.allIn_eq_true.1 h.2) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem signature_injective :
    Function.Injective fun i : Fin N => fun k : Fin 29 => pairing i (baseIndex k) := by
  intro i j h
  have hv : vecOf (sigsOf vectorOrbit sigT)[i.val]! = vecOf (sigsOf vectorOrbit sigT)[j.val]! := by
    funext k
    rw [vecOf_sig i.isLt, vecOf_sig j.isLt]
    split_ifs with hk
    · have := congrFun h ⟨k, hk⟩
      simp only at this
      rw [pairing_symm, this, pairing_symm]
    · rfl
  have e := vecOf_inj (sig_parts i i.isLt).1 (sig_parts j j.isLt).1 hv
  apply Fin.ext
  rw [← (sig_parts i i.isLt).2, ← (sig_parts j j.isLt).2, e]

theorem eq_one_of_fix_base
    {g : Equiv.Perm (Fin N)} (hg : g ∈ Pv)
    (hfix : ∀ k : Fin 29, g ⟨baseIndex k, baseIndex_lt k.isLt⟩ =
      ⟨baseIndex k, baseIndex_lt k.isLt⟩) : g = 1 := by
  ext i
  have h : (fun k : Fin 29 => pairing (g i) (baseIndex k)) =
      fun k : Fin 29 => pairing i (baseIndex k) := by
    funext k
    have := pairing_invariant hg i ⟨baseIndex k, baseIndex_lt k.isLt⟩
    rw [hfix k] at this
    exact this
  exact congrArg Fin.val (signature_injective h)

abbrev baseSet : Set (Fin N) := {x | ∃ k < 29, (x : ℕ) = baseIndex k}

theorem pv_inf_fixing_base :
    Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) baseSet = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgP, hgfix⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_bot]
  refine eq_one_of_fix_base hgP fun k => ?_
  have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).1 hgfix
    ⟨baseIndex k, baseIndex_lt k.isLt⟩ ⟨k, k.isLt, rfl⟩
  rwa [Equiv.Perm.smul_def] at this

theorem fam_on_invariant_form_and_separating_base :
    invariantFormᵀ = invariantForm ∧ invariantForm.det ≠ 0 ∧
      mAᵀ * invariantForm * mA = invariantForm ∧ mBᵀ * invariantForm * mB = invariantForm ∧
      (∀ g ∈ Pv, ∀ i j : Fin N, pairing (g i) (g j) = pairing i j) ∧
      (∀ i j : Fin 154, gramGraph.Adj i j ↔ i ≠ j ∧ pairing (spanIndex i) (spanIndex j) ≠ 0) ∧
      gramGraph.Connected ∧
      Function.Injective (fun i : Fin N => fun k : Fin 29 => pairing i (baseIndex k)) ∧
      Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) baseSet = ⊥ :=
  ⟨form_symm, form_det_ne_zero, form_parts.2.2.1, form_parts.2.2.2,
    fun _ hg => pairing_invariant hg, gramGraph_adj, gramGraph_connected, signature_injective,
    pv_inf_fixing_base⟩

end CFSG.ONSchreier
