
module

public import CFSG.Sporadic.Fi24.OrbitBase

public section

namespace CFSG.Sporadic.Fi24.Native

open Matrix CFSG.F3.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rowW_addW {d : ℕ} (X Y : Array W) (i : ℕ) (hi : i < d) :
    rowW (addW d X Y) i = (rowW X i).add (rowW Y i) := by
  unfold addW; rw [rowW_ofFn, dite_eq_left hi]; rfl

theorem RowsWF.addW (d : ℕ) {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) :
    RowsWF (Native.addW d X Y) := by
  intro x hx
  unfold Native.addW at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact W.wf_add (hX.row i.val) (hY.row i.val)

theorem addW_size (d : ℕ) (X Y : Array W) : (addW d X Y).size = d := by unfold addW; simp

theorem matW_addW {d : ℕ} {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) :
    matW d 781 (addW d X Y) = matW d 781 X + matW d 781 Y := by
  ext i j
  rw [Matrix.add_apply, matW_apply, matW_apply, matW_apply, rowW_addW X Y i.val i.isLt,
    W.val_add (hX.row _) (hY.row _)]

theorem RowsWF.negW {X : Array W} (hX : RowsWF X) : RowsWF (negW X) := by
  intro x hx
  unfold Native.negW at hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  rw [Array.getElem_map]
  exact W.wf_neg (hX _ (Array.getElem_mem _))

theorem negW_size (X : Array W) : (negW X).size = X.size := by unfold negW; simp

theorem matW_negW {d : ℕ} {X : Array W} (hX : RowsWF X) : matW d 781 (negW X) = -matW d 781 X := by
  ext i j
  rw [Matrix.neg_apply, matW_apply, matW_apply]
  unfold negW
  rw [rowW_map _ X rfl, W.val_neg (hX.row _)]
  rfl

theorem RowsWF.zeroW (d : ℕ) : RowsWF (zeroW d) := by
  intro x hx
  unfold Native.zeroW at hx
  rw [Array.mem_replicate] at hx
  rw [hx.2]; exact W.wf_zero

theorem zeroW_size (d : ℕ) : (zeroW d).size = d := by unfold zeroW; simp

theorem matW_zeroW (d : ℕ) : matW d 781 (zeroW d) = 0 := by
  ext i j
  rw [matW_apply]
  unfold zeroW rowW
  rw [Array.getElem?_replicate, ite_eq_left i.isLt]
  exact W.val_zero _

section Algebra

variable (mats : Array (Array W))

@[expose] noncomputable def matsAlg : Subalgebra (ZMod 3) (Matrix (Fin 781) (Fin 781) (ZMod 3)) :=
  Algebra.adjoin (ZMod 3) {M | ∃ i < mats.size, M = matW 781 781 (mats[i]?.getD #[])}

variable {mats}

@[expose] def MatsOK (mats : Array (Array W)) : Prop :=
  ∀ i < mats.size, canonRows 781 mats[i]! = true

end Algebra

theorem vecW_apply_mat {M : Array W} (hMw : RowsWF M) {x : W} (hx : x.wf = true) :
    vecW (frApply (frTable (transposeW 781 781 M)) x) = (matW 781 781 M).mulVec (vecW x) := by
  rw [vecW_frApply (RowsWF.transposeW (by norm_num) _ _) (transposeW_size _ _ _) hx,
    matW_transposeW (by norm_num) hMw, Matrix.transpose_transpose]

theorem W.isZero_vecW
    {a : W} (h : a.isZero = true) : vecW a = 0 := by
  unfold W.isZero at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hz : a = W.zero := by
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩,
      h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩ := h
    cases a
    simp_all [W.zero]
  rw [hz, vecW_zero]

theorem tritVal_trit
    {a : W} (ha : a.wf = true) (i : ℕ) : tritVal (a.trit i) = a.val i := by
  have h := W.not_both ha i
  unfold tritVal W.trit W.val bitVal
  cases hp : a.bitP i <;> cases hm : a.bitM i <;> simp_all

theorem rowW_projW
    {v : W} (hv : v.wf = true) {k : ℕ} (hk : k < 781) {i : ℕ} (hi : i < 781) :
    (rowW (projW 781 v k) i).wf = true ∧ ∀ j, (rowW (projW 781 v k) i).val j =
      (if j = i then 1 else 0) - (if j = k then v.val i else 0) := by
  unfold projW
  rw [rowW_ofFn, dite_eq_left hi]
  have h1 : (W.zero.setTrit i 1).wf = true := W.wf_setTrit W.wf_zero (by omega) (W.val_zero _) 1
  have h2 : (W.zero.setTrit k (v.trit i)).wf = true :=
    W.wf_setTrit W.wf_zero (by omega) (W.val_zero _) _
  refine ⟨W.wf_sub h1 h2, fun j => ?_⟩
  rw [W.val_sub h1 h2, W.val_setTrit (by omega) (W.val_zero _),
    W.val_setTrit (by omega) (W.val_zero _), tritVal_trit hv]
  simp only [W.val_zero]
  rfl

theorem mulVec_projW
    {v : W} (hv : v.wf = true) {k : ℕ} (hk : k < 781)
    (y : Fin 781 → ZMod 3) :
    (matW 781 781 (projW 781 v k)).mulVec y = y - y ⟨k, hk⟩ • vecW v := by
  funext r
  rw [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hrow : ∀ j : Fin 781, matW 781 781 (projW 781 v k) r j =
      (if j = r then 1 else 0) - (if j = (⟨k, hk⟩ : Fin 781) then v.val r.val else 0) := by
    intro j
    rw [matW_apply, (rowW_projW hv hk r.isLt).2 j.val]
    congr 1
    · by_cases h : j = r
      · subst h; simp
      · have : j.val ≠ r.val := fun e => h (Fin.ext e)
        simp [h, this]
    · by_cases h : j = (⟨k, hk⟩ : Fin 781)
      · subst h; simp
      · have : j.val ≠ k := fun e => h (Fin.ext e)
        simp [h, this]
  simp only [hrow, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ r,
    Finset.sum_ite_eq' Finset.univ (⟨k, hk⟩ : Fin 781)]
  simp only [Finset.mem_univ, ite_true]
  unfold vecW
  rw [mul_comm]

theorem rowW_push (S : Array W) (x : W) (i : ℕ) :
    rowW (S.push x) i = if i < S.size then rowW S i else if i = S.size then x else W.zero := by
  unfold rowW
  by_cases h1 : i < S.size
  · rw [ite_eq_left h1, Array.getElem?_push_lt h1, Array.getElem?_eq_getElem h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = S.size
    · subst h2; rw [ite_eq_left rfl, Array.getElem?_push_size]; rfl
    · rw [ite_eq_right h2, Array.getElem?_eq_none (by simp; omega)]; rfl

end CFSG.Sporadic.Fi24.Native
