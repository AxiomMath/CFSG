module

public import CFSG.Monster.Existence.WordRigid

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.AxisCount CFSG.Monster.Existence.Census Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

@[expose] def hnColRow (m : ℕ) : ℕ := Native.rowIdx (rigidRows[m]!).1 (rigidRows[m]!).2

@[expose] def hnRowCols : List (ℕ × ℤ) :=
  (List.range 13).map fun m => (98580 + 24 * hnColRow m + m, 1)

@[expose] def hnDiagCols : List (ℕ × ℤ) :=
  (List.range 24).map fun i => (i, (i : ℤ) + 1)

@[expose] def hnVecAD : Native.DVec := Native.DVec.ofList (hnDiagCols ++ hnRowCols)

@[expose] def hnVecJ : Native.DVec :=
  Native.DVec.ofList ((List.range 300).map fun k => (k, (1 : ℤ)))

theorem hn_rigidRows_length : rigidRows.length = 13 := by simp [rigidRows]

theorem hnVecAD_e : hnVecAD.e = 0 := rfl

theorem hnVecJ_e : hnVecJ.e = 0 := rfl

theorem hn_sum_range_ite (n j : ℕ) (hj : j < n) (P : ℕ → Prop) [DecidablePred P] (c : ℕ → ℤ) :
    ((List.range n).map fun m => if m = j ∧ P m then c m else 0).sum = if P j then c j else 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    by_cases hjn : j = n
    · subst hjn
      have h0 : ((List.range j).map fun m => if m = j ∧ P m then c m else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
        have := List.mem_range.1 hm
        exact ite_eq_right (show ¬ (m = j ∧ P m) from fun h => by omega)
      rw [h0, zero_add]
      by_cases hP : P j <;> simp [hP]
    · have hj' : j < n := by omega
      rw [ih hj']
      have : ¬ (n = j ∧ P n) := fun h => hjn h.1.symm
      rw [ite_eq_right this, add_zero]

theorem hn_sum_diagCols (k : ℕ) :
    (hnDiagCols.map fun t => if t.1 = k ∧ t.1 < 196884 then t.2 else 0).sum =
      if k < 24 then (k : ℤ) + 1 else 0 := by
  unfold hnDiagCols
  rw [List.map_map]
  by_cases hk : k < 24
  · rw [ite_eq_left hk]
    have := hn_sum_range_ite 24 k hk (fun m => m < 196884) (fun m => (m : ℤ) + 1)
    rw [ite_eq_left (by omega)] at this
    rw [← this]
    congr 1
  · rw [ite_eq_right hk]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 hm
    exact ite_eq_right (show ¬ (m = k ∧ _) from fun h => by omega)

theorem getD_hnVecAD_lt (k : ℕ) (hk : k < 300) :
    hnVecAD.D.getD k 0 = if k < 24 then (k : ℤ) + 1 else 0 := by
  unfold hnVecAD
  rw [HS.ofList_getD _ k (by omega), List.map_append, List.sum_append, hn_sum_diagCols]
  have h1 : (hnRowCols.map fun t => if t.1 = k ∧ t.1 < 196884 then t.2 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    unfold hnRowCols at ht
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ht
    exact ite_eq_right (show ¬ (98580 + 24 * hnColRow m + m = k ∧ _) from fun h => by omega)
  rw [h1, add_zero]

theorem getD_hnVecAD_X (k : ℕ) (hk1 : 300 ≤ k) (hk2 : k < 98580) : hnVecAD.D.getD k 0 = 0 := by
  unfold hnVecAD
  rw [HS.ofList_getD _ k (by omega), List.map_append, List.sum_append]
  have h1 : (hnDiagCols.map fun t => if t.1 = k ∧ t.1 < 196884 then t.2 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    unfold hnDiagCols at ht
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ht
    have := List.mem_range.1 hm
    exact ite_eq_right (show ¬ (m = k ∧ _) from fun h => by omega)
  have h2 : (hnRowCols.map fun t => if t.1 = k ∧ t.1 < 196884 then t.2 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    unfold hnRowCols at ht
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ht
    exact ite_eq_right (show ¬ (98580 + 24 * hnColRow m + m = k ∧ _) from fun h => by omega)
  rw [h1, h2, add_zero]

theorem getD_hnVecAD_W (r j : ℕ) (hr : r < 4096) (hj : j < 24) :
    hnVecAD.D.getD (98580 + 24 * r + j) 0 = if j < 13 ∧ hnColRow j = r then 1 else 0 := by
  unfold hnVecAD
  rw [HS.ofList_getD _ _ (by omega), List.map_append, List.sum_append]
  have h1 : (hnDiagCols.map fun t =>
      if t.1 = 98580 + 24 * r + j ∧ t.1 < 196884 then t.2 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    unfold hnDiagCols at ht
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ht
    have := List.mem_range.1 hm
    exact ite_eq_right (show ¬ (m = 98580 + 24 * r + j ∧ _) from fun h => by omega)
  rw [h1, zero_add]
  unfold hnRowCols
  rw [List.map_map]
  have hcongr : ∀ m ∈ List.range 13,
      ((fun t : ℕ × ℤ => if t.1 = 98580 + 24 * r + j ∧ t.1 < 196884 then t.2 else 0) ∘
        fun m => (98580 + 24 * hnColRow m + m, (1 : ℤ))) m =
      if m = j ∧ hnColRow m = r then 1 else 0 := by
    intro m hm
    have hm13 := List.mem_range.1 hm
    simp only [Function.comp_apply]
    by_cases h : m = j ∧ hnColRow m = r
    · obtain ⟨h1, h2⟩ := h
      have hc : 98580 + 24 * hnColRow m + m = 98580 + 24 * r + j ∧
          98580 + 24 * hnColRow m + m < 196884 := ⟨by omega, by omega⟩
      have e1 : (if 98580 + 24 * hnColRow m + m = 98580 + 24 * r + j ∧
          98580 + 24 * hnColRow m + m < 196884 then (1 : ℤ) else 0) = 1 := ite_eq_left hc
      have e2 : (if m = j ∧ hnColRow m = r then (1 : ℤ) else 0) = 1 := ite_eq_left ⟨h1, h2⟩
      show (if 98580 + 24 * hnColRow m + m = 98580 + 24 * r + j ∧
          98580 + 24 * hnColRow m + m < 196884 then (1 : ℤ) else 0) = _
      rw [e1, e2]
    · have e1 : (if 98580 + 24 * hnColRow m + m = 98580 + 24 * r + j ∧
          98580 + 24 * hnColRow m + m < 196884 then (1 : ℤ) else 0) = 0 :=
        ite_eq_right fun hh => h ⟨by omega, by omega⟩
      have e2 : (if m = j ∧ hnColRow m = r then (1 : ℤ) else 0) = 0 := ite_eq_right h
      show (if 98580 + 24 * hnColRow m + m = 98580 + 24 * r + j ∧
          98580 + 24 * hnColRow m + m < 196884 then (1 : ℤ) else 0) = _
      rw [e1, e2]
  rw [List.map_congr_left hcongr]
  by_cases hj13 : j < 13
  · have := hn_sum_range_ite 13 j hj13 (fun m => hnColRow m = r) (fun _ => 1)
    rw [this]
    by_cases hc : hnColRow j = r <;> simp [hj13, hc]
  · rw [ite_eq_right (fun h => hj13 h.1)]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 hm
    exact ite_eq_right (show ¬ (m = j ∧ _) from fun h => by omega)

theorem hn_aIdx_lt_24_iff (i j : Fin 24) : Native.aIdx i j < 24 ↔ (i : ℕ) = j := by
  unfold Native.aIdx
  by_cases h : (i : ℕ) = j
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => i.2⟩
  · rw [ite_eq_right h]
    exact ⟨fun hh => by omega, fun hh => absurd hh h⟩

theorem interpA_hnVecAD (i j : Fin 24) :
    ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) i j =
      if i = j then ((i : ℕ) : ℚ) + 1 else 0 := by
  have h := getD_hnVecAD_lt (Native.aIdx i j) (Native.aIdx_spec i j i.2 j.2).1
  simp only [interpA, Matrix.of_apply, hnVecAD_e, pow_zero, div_one]
  rw [h]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left ((hn_aIdx_lt_24_iff i i).2 rfl), ite_eq_left rfl]
    simp [Native.aIdx]
  · have hn : ¬ Native.aIdx i j < 24 := fun hh => hij (Fin.ext ((hn_aIdx_lt_24_iff i j).1 hh))
    rw [ite_eq_right hn, ite_eq_right hij]
    simp

theorem interpX_hnVecAD (c : ShortIdx) : interpX hnVecAD c = 0 := by
  have h := posOf_lt c
  unfold interpX
  rw [getD_hnVecAD_X (300 + posOf c) (by omega) (by omega)]
  simp

theorem hnColRow_lt (m : ℕ) : hnColRow m < 4096 := rowIdx_lt _ _

theorem interpW_hnVecAD (b : SpinIdx) (j : Fin 24) :
    interpW hnVecAD b j = if (j : ℕ) < 13 ∧ hnColRow j = rowOf b then 1 else 0 := by
  unfold interpW
  simp only [Matrix.of_apply, hnVecAD_e, pow_zero, div_one]
  rw [getD_hnVecAD_W (rowOf b) j (rowOf_lt b) j.2]
  by_cases h : (j : ℕ) < 13 ∧ hnColRow j = rowOf b
  · rw [ite_eq_left h, ite_eq_left h]
    simp
  · rw [ite_eq_right h, ite_eq_right h]
    simp

theorem interpW_hnVecAD_row (m : ℕ) (hm : m < 13) (b : SpinIdx) :
    interpW hnVecAD b ⟨m, by omega⟩ = if b = spinOfRow (hnColRow m) then 1 else 0 := by
  rw [interpW_hnVecAD]
  have hlt := hnColRow_lt m
  by_cases h : b = spinOfRow (hnColRow m)
  · have hr : hnColRow m = rowOf b := by
      rw [h, rowOf_spinOfRow hlt]
    rw [ite_eq_left ⟨hm, hr⟩, ite_eq_left h]
  · have hr : ¬ hnColRow m = rowOf b := fun hr => h (by rw [hr, spinOfRow_rowOf])
    rw [ite_eq_right (fun hh => hr hh.2), ite_eq_right h]

theorem interpA_hnVecJ (i j : Fin 24) :
    ((interpA hnVecJ : symMat) : Matrix (Fin 24) (Fin 24) ℚ) i j = 1 := by
  have hlt := (Native.aIdx_spec i j i.2 j.2).1
  have hd : hnVecJ.D.getD (Native.aIdx i j) 0 = 1 := by
    unfold hnVecJ
    rw [HS.ofList_getD _ _ (by omega), List.map_map]
    have := hn_sum_range_ite 300 (Native.aIdx i j) hlt (fun m => m < 196884) (fun _ => 1)
    rw [ite_eq_left (by omega)] at this
    refine Eq.trans ?_ this
    congr 1
  simp only [interpA, Matrix.of_apply, hnVecJ_e, pow_zero, div_one]
  rw [hd]
  simp

theorem eq_one_of_fix_AD_J
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis)
    (h₁ : g (interp hnVecAD) = interp hnVecAD) (h₂ : g (interp hnVecJ) = interp hnVecJ) :
    g = 1 := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
  set s := (p.1.1 : Matrix SpinIdx SpinIdx ℚ) with hs
  set L := mat p.1.2 with hL
  have hLLt : L * Lᵀ = 1 := mat_mul_transpose p.1.2
  have hA0 : Lᵀ * ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) * L =
      ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) := by
    have := congrArg (fun x : SpaceB => x.1) h₁
    exact (coe_thetaA L (interpA hnVecAD)).symm.trans (congrArg Subtype.val this)
  have hJ : Lᵀ * ((interpA hnVecJ : symMat) : Matrix (Fin 24) (Fin 24) ℚ) * L =
      ((interpA hnVecJ : symMat) : Matrix (Fin 24) (Fin 24) ℚ) := by
    have := congrArg (fun x : SpaceB => x.1) h₂
    exact (coe_thetaA L (interpA hnVecJ)).symm.trans (congrArg Subtype.val this)
  have hW : sᵀ * interpW hnVecAD * L = interpW hnVecAD := congrArg (fun x : SpaceB => x.2.2) h₁
  have hcomm : ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) * L =
      L * ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) := by
    calc ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) * L
        = (L * Lᵀ) * ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) * L := by
          rw [hLLt, Matrix.one_mul]
      _ = L * (Lᵀ * ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) * L) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA0]
  have hLoff : ∀ i j : Fin 24, i ≠ j → L i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun hcomm i) j
    have e1 : (((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ) * L) i j =
        (((i : ℕ) : ℚ) + 1) * L i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [interpA_hnVecAD, ite_eq_left rfl]
      · intro k _ hk
        rw [interpA_hnVecAD, ite_eq_right (Ne.symm hk), zero_mul]
      · simp
    have e2 : (L * ((interpA hnVecAD : symMat) : Matrix (Fin 24) (Fin 24) ℚ)) i j =
        L i j * (((j : ℕ) : ℚ) + 1) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [interpA_hnVecAD, ite_eq_left rfl]
      · intro k _ hk
        rw [interpA_hnVecAD, ite_eq_right hk, mul_zero]
      · simp
    rw [e1, e2] at h1
    have h2 : (((i : ℕ) : ℚ) - ((j : ℕ) : ℚ)) * L i j = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Fin.ext (by exact_mod_cast sub_eq_zero.1 h3)) hij
    · exact h3
  have hdiag : ∀ i : Fin 24, L i i * L i i = 1 := by
    intro i
    have h1 := congrFun (congrFun hLLt i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · simpa using h1
    · intro k _ hk
      rw [hLoff i k (Ne.symm hk), zero_mul]
    · simp
  have hcol : ∀ i : Fin 24, ∑ k, L k i = L i i := fun i =>
    Finset.sum_eq_single i (fun k _ hk => hLoff k i hk) (by simp)
  have hLJ : ∀ i j : Fin 24, L i i * L j j = 1 := by
    intro i j
    have h1 := congrFun (congrFun hJ i) j
    simp only [Matrix.mul_apply, interpA_hnVecJ, mul_one, Matrix.transpose_apply] at h1
    have e : ∑ l, (∑ k, L k i) * L l j = L i i * L j j := by
      rw [← Finset.mul_sum, hcol i, hcol j]
    rw [← e]
    exact h1
  set μ := L 0 0 with hμ
  have hμμ : μ * μ = 1 := hLJ 0 0
  have hLμ : L = μ • (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
    ext i j
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, mul_one]
      have hne : L 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hμμ
      exact mul_right_cancel₀ hne ((hLJ i 0).trans hμμ.symm)
    · rw [ite_eq_right hij, mul_zero]
      exact hLoff i j hij
  have hrow : ∀ x ∈ rigidRows, ∀ a : SpinIdx,
      s (boolZ x.1, π₀ (toC x.2)) a = μ * (if a = (boolZ x.1, π₀ (toC x.2)) then 1 else 0) := by
    intro x hx a
    obtain ⟨m, hm, hmx⟩ := List.mem_iff_getElem.1 hx
    have hm13 : m < 13 := by rw [← hn_rigidRows_length]; exact hm
    have hrowm : spinOfRow (hnColRow m) = (boolZ x.1, π₀ (toC x.2)) := by
      unfold hnColRow
      rw [spinOfRow_rowIdx, getElem!_pos rigidRows m hm, hmx]
    rw [hLμ, Matrix.mul_smul, Matrix.mul_one] at hW
    have h1 := congrFun (congrFun hW a) ⟨m, by omega⟩
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
      interpW_hnVecAD_row m hm13, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, hrowm] at h1
    calc s (boolZ x.1, π₀ (toC x.2)) a
        = s (boolZ x.1, π₀ (toC x.2)) a * (μ * μ) := by rw [hμμ, mul_one]
      _ = μ * (μ * s (boolZ x.1, π₀ (toC x.2)) a) := by ring
      _ = _ := by rw [h1]
  rcases mul_self_eq_one_iff.1 hμμ with hμ1 | hμ1
  · have hL1 : p.1.2 = 1 := mat_injective (by rw [← hL, hLμ, hμ1, one_smul, mat_one])
    have hp1 : p = 1 := eq_one_of_snd_eq_one p hL1 fun x hx a => by
      show s (boolZ x.1, π₀ (toC x.2)) a = _
      rw [hrow x hx a, hμ1, one_mul]
    rw [hp1, thetaEquiv_one]
  · have hL1 : p.1.2 = negOneO := mat_injective (by
      rw [← hL, hLμ, hμ1, neg_one_smul, mat_negOneO])
    have hp1 : p * negPair = 1 := by
      refine eq_one_of_snd_eq_one _ ?_ fun x hx a => ?_
      · rw [mul_negPair_snd, hL1, negOneO_mul_self]
      · show (((p * negPair : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ)
          (boolZ x.1, π₀ (toC x.2)) a = _
        rw [mul_negPair_fst, Matrix.neg_apply]
        show -s (boolZ x.1, π₀ (toC x.2)) a = _
        rw [hrow x hx a, hμ1]
        ring
    rw [← thetaEquiv_mul_negPair p, hp1, thetaEquiv_one]

theorem eq_one_of_fix_four
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) (h₁ : g aStar = aStar)
    (h₂ : g aStarMinus = aStarMinus) (h₃ : g (interp hnVecAD) = interp hnVecAD)
    (h₄ : g (interp hnVecJ) = interp hnVecJ) : g = 1 :=
  eq_one_of_fix_AD_J (mem_Gvis_of_fix_axes hg h₁ h₂) h₃ h₄

theorem eq_of_fix_four
    {a b : SpaceB ≃ₗ[ℚ] SpaceB} (ha : a ∈ AutO) (hb : b ∈ AutO)
    (h₁ : a aStar = b aStar) (h₂ : a aStarMinus = b aStarMinus)
    (h₃ : a (interp hnVecAD) = b (interp hnVecAD)) (h₄ : a (interp hnVecJ) = b (interp hnVecJ)) :
    a = b := by
  have hfix : ∀ v, a v = b v → (b⁻¹ * a) v = v := fun v hv => by
    rw [LinearEquiv.mul_apply, hv]
    exact b.symm_apply_apply v
  have h1 : b⁻¹ * a = 1 :=
    eq_one_of_fix_four (mul_mem (inv_mem hb) ha) (hfix _ h₁) (hfix _ h₂) (hfix _ h₃) (hfix _ h₄)
  exact (inv_mul_eq_one.1 h1).symm

theorem eq_of_fix_two
    {a b : SpaceB ≃ₗ[ℚ] SpaceB} (ha : a ∈ Gvis) (hb : b ∈ Gvis)
    (h₃ : a (interp hnVecAD) = b (interp hnVecAD)) (h₄ : a (interp hnVecJ) = b (interp hnVecJ)) :
    a = b := by
  have hfix : ∀ v, a v = b v → (b⁻¹ * a) v = v := fun v hv => by
    rw [LinearEquiv.mul_apply, hv]
    exact b.symm_apply_apply v
  have h1 : b⁻¹ * a = 1 :=
    eq_one_of_fix_AD_J (Gvis.mul_mem (Gvis.inv_mem hb) ha) (hfix _ h₃) (hfix _ h₄)
  exact (inv_mul_eq_one.1 h1).symm

@[expose, noinline] def checkP4 (p₁ p₂ : List Native.PGen) : Bool :=
  (Native.evalPrep HS.hsCtx p₁ HS.axisP).eqv (Native.evalPrep HS.hsCtx p₂ HS.axisP) &&
    (Native.evalPrep HS.hsCtx p₁ HS.axisM).eqv (Native.evalPrep HS.hsCtx p₂ HS.axisM) &&
    (Native.evalPrep HS.hsCtx p₁ hnVecAD).eqv (Native.evalPrep HS.hsCtx p₂ hnVecAD) &&
    (Native.evalPrep HS.hsCtx p₁ hnVecJ).eqv (Native.evalPrep HS.hsCtx p₂ hnVecJ)

@[expose, noinline] def checkP2 (p₁ p₂ : List Native.PGen) : Bool :=
  (Native.evalPrep HS.hsCtx p₁ hnVecAD).eqv (Native.evalPrep HS.hsCtx p₂ hnVecAD) &&
    (Native.evalPrep HS.hsCtx p₁ hnVecJ).eqv (Native.evalPrep HS.hsCtx p₂ hnVecJ)

theorem wordLin_eq_of_checkP4
    {w₁ w₂ : List Native.Gen}
    (hv : (w₁ ++ w₂).all Native.Gen.validB = true) (h : checkP4 (HS.pw w₁) (HS.pw w₂) = true) :
    wordLin w₁ = wordLin w₂ := by
  have hw₁ : w₁.all Native.Gen.validB = true := by
    simp only [List.all_append, Bool.and_eq_true] at hv
    exact hv.1
  have hw₂ : w₂.all Native.Gen.validB = true := by
    simp only [List.all_append, Bool.and_eq_true] at hv
    exact hv.2
  have key : ∀ v : Native.DVec,
      (Native.evalPrep HS.hsCtx (HS.pw w₁) v).eqv (Native.evalPrep HS.hsCtx (HS.pw w₂) v) = true →
        wordLin w₁ (interp v) = wordLin w₂ (interp v) := fun v hv' => by
    have := eqv_sound hv'
    rwa [HS.interp_evalPrep_pw hw₁, HS.interp_evalPrep_pw hw₂] at this
  unfold checkP4 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hP, hM⟩, hAD⟩, hJ⟩ := h
  refine eq_of_fix_four (Gmat_le_AutO (wordLin_mem_Gmat w₁)) (Gmat_le_AutO (wordLin_mem_Gmat w₂))
    ?_ ?_ (key _ hAD) (key _ hJ)
  · have := key _ hP
    rwa [HS.interp_axisP] at this
  · have := key _ hM
    rwa [HS.interp_axisM] at this

theorem wordLin_eq_of_checkP2
    {w₁ w₂ : List Native.Gen} (hτ₁ : ∀ g ∈ w₁, ¬ g = .tau)
    (hτ₂ : ∀ g ∈ w₂, ¬ g = .tau) (hv : (w₁ ++ w₂).all Native.Gen.validB = true)
    (h : checkP2 (HS.pw w₁) (HS.pw w₂) = true) : wordLin w₁ = wordLin w₂ := by
  have hw₁ : w₁.all Native.Gen.validB = true := by
    simp only [List.all_append, Bool.and_eq_true] at hv
    exact hv.1
  have hw₂ : w₂.all Native.Gen.validB = true := by
    simp only [List.all_append, Bool.and_eq_true] at hv
    exact hv.2
  have key : ∀ v : Native.DVec,
      (Native.evalPrep HS.hsCtx (HS.pw w₁) v).eqv (Native.evalPrep HS.hsCtx (HS.pw w₂) v) = true →
        wordLin w₁ (interp v) = wordLin w₂ (interp v) := fun v hv' => by
    have := eqv_sound hv'
    rwa [HS.interp_evalPrep_pw hw₁, HS.interp_evalPrep_pw hw₂] at this
  unfold checkP2 at h
  simp only [Bool.and_eq_true] at h
  exact eq_of_fix_two (wordLin_mem_Gvis w₁ hτ₁) (wordLin_mem_Gvis w₂ hτ₂) (key _ h.1) (key _ h.2)

@[expose] def hnDiffA (i j : ℕ) (u w : Native.DVec) : Bool :=
  decide (u.D.getD (Native.aIdx i j) 0 * 2 ^ w.e ≠ w.D.getD (Native.aIdx i j) 0 * 2 ^ u.e)

theorem hn_interp_ne_of_diffA
    {i j : Fin 24} {u w : Native.DVec} (h : hnDiffA i j u w = true) :
    interp u ≠ interp w := by
  intro heq
  have h1 := congrArg (fun x : SpaceB => ((x.1 : symMat) : Matrix (Fin 24) (Fin 24) ℚ) i j) heq
  simp only [interp, interpA, Matrix.of_apply] at h1
  unfold hnDiffA at h
  rw [decide_eq_true_eq] at h
  apply h
  have h2 : ((u.D.getD (Native.aIdx i j) 0 : ℤ) : ℚ) * 2 ^ w.e =
      ((w.D.getD (Native.aIdx i j) 0 : ℤ) : ℚ) * 2 ^ u.e := by
    field_simp at h1
    linarith
  exact_mod_cast h2

theorem hn_wordLin_ne_one_of_diffA
    {w : List Native.Gen} (hw : w.all Native.Gen.validB = true)
    {i j : Fin 24} (h : hnDiffA i j (Native.evalPrep HS.hsCtx (HS.pw w) HS.axisP) HS.axisP = true) :
    wordLin w ≠ 1 := by
  intro h1
  apply hn_interp_ne_of_diffA h
  rw [HS.interp_evalPrep_pw hw, h1, HS.interp_axisP]
  rfl

end CFSG.Monster.Existence
