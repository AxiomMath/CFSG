module

public import CFSG.Sporadic.Schreier.Co1ElemThreeGroup

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply toVecD toVecD_injective toVecD_xor
  toVecD_zero foldl_xor_toVecD rowsMatrix_mulRows rowsMatrix_transposeRows)
open ElemThree Matrix

noncomputable abbrev zM : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (ThreeLocal.z : Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem rowsMatrix_add (X Y : Native.Rows) :
    rowsMatrix 24 (Native.add X Y) = rowsMatrix 24 X + rowsMatrix 24 Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold Native.add
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor, Pi.add_apply]

theorem zM_sq :
    zM * zM = zM + 1 := by
  have h := eigen_check
  simp only [Native.eigenCheck, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : rowsMatrix 24 (Native.mul Native.zR Native.zR) = zM * zM := by
    rw [rep_z.mul rep_z, Units.val_mul]
  rw [h.1.1.1.2, rowsMatrix_add, rep_z, MRep.one, Units.val_one] at h1
  exact h1.symm

theorem zM_mulVec_ne_self
    {v : Vec24} (hv : v ≠ 0) : zM *ᵥ v ≠ v := by
  intro h
  apply hv
  have h2 : (zM * zM) *ᵥ v = v := by rw [← mulVec_mulVec, h, h]
  rw [zM_sq, add_mulVec, one_mulVec, h] at h2
  have : v + v = 0 := CharTwo.add_self_eq_zero v
  rw [this] at h2
  exact h2.symm

theorem zM_cube :
    zM ^ 3 = 1 := by
  rw [pow_succ, pow_two, zM_sq, add_mul, one_mul, zM_sq]
  have : zM + zM = 0 := CharTwo.add_self_eq_zero zM
  rw [add_comm, ← add_assoc, this, zero_add]

theorem zM_sq_mulVec_ne_self
    {v : Vec24} (hv : v ≠ 0) : (zM ^ 2) *ᵥ v ≠ v := by
  intro h
  apply zM_mulVec_ne_self hv
  have h3 : (zM ^ 3) *ᵥ v = zM *ᵥ v := by
    rw [pow_succ', ← mulVec_mulVec, h]
  rw [zM_cube, one_mulVec] at h3
  exact h3.symm

theorem zM_pow_mulVec_eq_self
    {v : Vec24} (hv : v ≠ 0) {m : ℕ} (h : (zM ^ m) *ᵥ v = v) :
    m % 3 = 0 := by
  have hm : zM ^ m = zM ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, zM_cube, one_pow, one_mul]
  rw [hm] at h
  have : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : m % 3
  · rfl
  · exact absurd (by simpa using h) (zM_mulVec_ne_self hv)
  · exact absurd h (zM_sq_mulVec_ne_self hv)

theorem toVecD_shift {k : ℕ} (hk : k < 24) : toVecD 24 (1 <<< k) = e ⟨k, hk⟩ := by
  funext i
  rw [CFSG.Sporadic.SmallF2.toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp
  · have h' : k ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem cast_mod_two_smul (n : ℕ) (v : Vec24) :
    (((n % 2 : ℕ) : ZMod 2) • v) = if n % 2 = 1 then v else 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem toVecD_foldl_xor {ι : Type*} (l : List ι) (P : ι → Prop) [DecidablePred P] (g : ι → ℕ)
    (init : ℕ) :
    toVecD 24 (l.foldl (fun acc k => if P k then acc ^^^ g k else acc) init) =
      toVecD 24 init + (l.map fun k => if P k then toVecD 24 (g k) else 0).sum := by
  induction l generalizing init with
  | nil => simp
  | cons k l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    split_ifs <;> simp [toVecD_xor]

theorem f4Vec_eq (cs : List ℕ) :
    f4Vec cs = toVecD 24 (Native.f4Lo cs ^^^ Native.f4Hi cs) := by
  rw [toVecD_xor]
  unfold Native.f4Lo Native.f4Hi
  rw [toVecD_foldl_xor, toVecD_foldl_xor, toVecD_zero, zero_add, zero_add, ← Fin.sum_univ_def,
    ← Fin.sum_univ_def]
  unfold f4Vec
  rw [Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [cast_mod_two_smul, toVecD_shift (by have := k.isLt; omega)]
    rfl
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [cast_mod_two_smul]
    split_ifs
    · rw [← rep_z.mulVec, toVecD_shift (by have := k.isLt; omega)]
      rfl
    · rfl

theorem q_eq
    (j : Fin 12) : q j = toVecD 24 (Native.qNat j.val) := f4Vec_eq _

theorem a_zero :
    a 0 = ThreeLocal.z := by
  have h := eigen_check
  simp only [Native.eigenCheck, Bool.and_eq_true, beq_iff_eq] at h
  have h1 := a_rep 0
  rw [show (0 : Fin 6).val = 0 from rfl, h.1.2] at h1
  exact h1.eq rep_z

theorem toVecD_zPow
    (e v : ℕ) : toVecD 24 (Native.zPow e v) = (zM ^ e) *ᵥ toVecD 24 v := by
  induction e generalizing v with
  | zero => simp [Native.zPow]
  | succ e ih =>
    unfold Native.zPow at ih ⊢
    rw [Function.iterate_succ_apply, ih, ← rep_z.mulVec, mulVec_mulVec, ← pow_succ]

theorem gam_lt
    (j : Fin 12) (i : Fin 6) : Native.gam j.val i.val < 3 := by
  have h := eigen_check
  simp only [Native.eigenCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact (h.1.1.1.1 i.val i.isLt j.val j.isLt).2

theorem γ_val
    (j : Fin 12) (i : Fin 6) : (γ j i).val = Native.gam j.val i.val := by
  have h := gam_lt j i
  unfold γ
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h

theorem a_mulVec_q
    (i : Fin 6) (j : Fin 12) :
    ((a i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ q j = (zM ^ (γ j i).val) *ᵥ q j := by
  have h := eigen_check
  simp only [Native.eigenCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  have h1 := (h.1.1.1.1 i.val i.isLt j.val j.isLt).1
  rw [q_eq, (a_rep i).mulVec, h1, toVecD_zPow, γ_val]

theorem qMat_inv :
    rowsMatrix 24 (Native.inv Native.qMat) * rowsMatrix 24 Native.qMat = 1 ∧
    rowsMatrix 24 Native.qMat * rowsMatrix 24 (Native.inv Native.qMat) = 1 := by
  have h := eigen_check
  simp only [Native.eigenCheck, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : rowsMatrix 24 (Native.mul (Native.inv Native.qMat) Native.qMat) =
      rowsMatrix 24 (Native.inv Native.qMat) * rowsMatrix 24 Native.qMat :=
    rowsMatrix_mulRows 24 _ _
  have h2 : rowsMatrix 24 (Native.mul Native.qMat (Native.inv Native.qMat)) =
      rowsMatrix 24 Native.qMat * rowsMatrix 24 (Native.inv Native.qMat) :=
    rowsMatrix_mulRows 24 _ _
  rw [h.1.1.2, MRep.one, Units.val_one] at h1
  rw [h.2, MRep.one, Units.val_one] at h2
  exact ⟨h1.symm, h2.symm⟩

theorem qMat_col (k : Fin 24) :
    (rowsMatrix 24 Native.qMat).col k = toVecD 24 (Native.qCols[k.val]?.getD 0) := by
  funext i
  change rowsMatrix 24 Native.qMat i k = _
  unfold Native.qMat
  rw [rowsMatrix_transposeRows, Matrix.transpose_apply, rowsMatrix_apply]

theorem qCols_get
    (j : Fin 12) (e : Fin 2) :
    toVecD 24 (Native.qCols[(finProdFinEquiv (j, e)).val]?.getD 0) = (zM ^ e.val) *ᵥ q j := by
  have hk : (finProdFinEquiv (j, e)).val = e.val + 2 * j.val := rfl
  have hlt : e.val + 2 * j.val < 24 := by have := e.isLt; have := j.isLt; omega
  unfold Native.qCols
  rw [Array.getElem?_ofFn, hk]
  simp only [hlt, ↓reduceDIte, Option.getD_some]
  have hd : (e.val + 2 * j.val) / 2 = j.val := by omega
  have he : e.val = 0 ∨ e.val = 1 := by have := e.isLt; omega
  rcases he with he | he
  · have hm : (e.val + 2 * j.val) % 2 = 0 := by omega
    simp only [hm, hd, ↓reduceIte]
    rw [he, pow_zero, one_mulVec, q_eq]
  · have hm : (e.val + 2 * j.val) % 2 = 1 := by omega
    simp only [hm, hd, one_ne_zero, ↓reduceIte]
    rw [he, pow_one, q_eq]
    exact (rep_z.mulVec _).symm

theorem qMat_mulVec
    (g : Fin 24 → ZMod 2) :
    rowsMatrix 24 Native.qMat *ᵥ g =
      ∑ p : Fin 12 × Fin 2, g (finProdFinEquiv p) • ((zM ^ p.2.val) *ᵥ q p.1) := by
  rw [Matrix.mulVec_eq_sum, ← (finProdFinEquiv (m := 12) (n := 2)).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← qCols_get, ← qMat_col, op_smul_eq_smul]
  rfl

theorem linearIndependent_q :
    LinearIndependent (ZMod 2) (fun p : Fin 12 × Fin 2 => (zM ^ p.2.val) *ᵥ q p.1) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg p
  have key : ∀ f : Fin 12 × Fin 2 → ZMod 2, rowsMatrix 24 Native.qMat *ᵥ
      (f ∘ (finProdFinEquiv (m := 12) (n := 2)).symm) = ∑ p, f p • ((zM ^ p.2.val) *ᵥ q p.1) := by
    intro f
    rw [qMat_mulVec]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Function.comp_apply, Equiv.symm_apply_apply]
  have h1 : f ∘ (finProdFinEquiv (m := 12) (n := 2)).symm =
      g ∘ (finProdFinEquiv (m := 12) (n := 2)).symm := by
    rw [← one_mulVec (f ∘ _), ← one_mulVec (g ∘ _), ← qMat_inv.1, ← mulVec_mulVec,
      ← mulVec_mulVec, key, key, hfg]
  have := congrFun h1 (finProdFinEquiv p)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using this

theorem span_q :
    Submodule.span (ZMod 2) (Set.range fun p : Fin 12 × Fin 2 => (zM ^ p.2.val) *ᵥ q p.1) =
      ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = rowsMatrix 24 Native.qMat *ᵥ (rowsMatrix 24 (Native.inv Native.qMat) *ᵥ v) := by
    rw [mulVec_mulVec, qMat_inv.2, one_mulVec]
  rw [hv, qMat_mulVec]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

@[expose] noncomputable def plane (j : Fin 12) : Submodule (ZMod 2) Vec24 :=
  Submodule.span (ZMod 2) {q j, zM *ᵥ q j}

theorem q_mem_plane (j : Fin 12) : q j ∈ plane j :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem zq_mem_plane (j : Fin 12) : zM *ᵥ q j ∈ plane j :=
  Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

theorem zM_mulVec_mem_plane
    {j : Fin 12} {v : Vec24} (hv : v ∈ plane j) :
    zM *ᵥ v ∈ plane j := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec, zM_sq, add_mulVec, one_mulVec]
  refine Submodule.mem_span_pair.mpr ⟨β, α + β, ?_⟩
  rw [add_smul, smul_add]
  abel

theorem zM_pow_mulVec_mem_plane
    {j : Fin 12} {v : Vec24} (hv : v ∈ plane j) (m : ℕ) :
    (zM ^ m) *ᵥ v ∈ plane j := by
  induction m with
  | zero => rwa [pow_zero, one_mulVec]
  | succ m ih => rw [pow_succ', ← mulVec_mulVec]; exact zM_mulVec_mem_plane ih

theorem a_mul_z
    (i : Fin 6) :
    ((a i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) * zM =
      zM * ((a i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have h : a i * a 0 = a 0 * a i := a_comm i 0
  rw [a_zero] at h
  have := congrArg Units.val h
  rwa [Units.val_mul, Units.val_mul] at this

theorem a_mulVec_plane
    (i : Fin 6) {j : Fin 12} {v : Vec24} (hv : v ∈ plane j) :
    ((a i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = (zM ^ (γ j i).val) *ᵥ v := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [mulVec_add, mulVec_smul, mulVec_smul, mulVec_add, mulVec_smul, mulVec_smul, a_mulVec_q,
    mulVec_mulVec, a_mul_z, ← mulVec_mulVec, a_mulVec_q, mulVec_mulVec, mulVec_mulVec,
    ← pow_succ, ← pow_succ']

theorem a_mulVec_mem_plane
    (i : Fin 6) {j : Fin 12} {v : Vec24} (hv : v ∈ plane j) :
    ((a i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ plane j := by
  rw [a_mulVec_plane i hv]
  exact zM_pow_mulVec_mem_plane hv _

theorem list_prod_mulVec_mem_plane {j : Fin 12} (l : List GL24)
    (hl : ∀ x ∈ l, ∀ v ∈ plane j, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ plane j)
    {v : Vec24} (hv : v ∈ plane j) :
    ((l.prod : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ plane j := by
  induction l generalizing v with
  | nil => rwa [List.prod_nil, Units.val_one, one_mulVec]
  | cons x l ih =>
    rw [List.prod_cons, Units.val_mul, ← mulVec_mulVec]
    exact hl x List.mem_cons_self _ (ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hv)

theorem E_mulVec_mem_plane
    {j : Fin 12} {x : GL24} (hx : x ∈ E) {v : Vec24}
    (hv : v ∈ plane j) : ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ plane j := by
  obtain ⟨b, rfl⟩ : x ∈ eHom.range := eHom_range ▸ hx
  change ((eProd b.toAdd : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ plane j
  unfold eProd
  refine list_prod_mulVec_mem_plane _ (fun y hy w hw => ?_) hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  clear hy
  induction (b.toAdd i).val generalizing w with
  | zero => rwa [pow_zero, Units.val_one, one_mulVec]
  | succ m ih =>
    rw [pow_succ, Units.val_mul, ← mulVec_mulVec]
    exact ih _ (a_mulVec_mem_plane i hw)

end CFSG.Sporadic.Co1Schreier
