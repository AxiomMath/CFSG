
module

public import CFSG.Sporadic.Fi24.InvSpec
public import CFSG.Sporadic.Fi24.SepSpecBase
public import CFSG.Sporadic.Fi24.ExtCertInputs
public import CFSG.Certificates.Kernel.Spor.Fi24FixInit

public section

namespace CFSG.Sporadic.Fi24.Native

open Matrix CFSG.F3.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ZeroFrom (d : ℕ) (X : Array W) : Prop := ∀ i j, d ≤ j → (rowW X i).val j = 0

theorem ZeroFrom.mono {d d' : ℕ} {X : Array W} (hd : d ≤ d') (h : ZeroFrom d X) :
    ZeroFrom d' X := fun i j hj => h i j (le_trans hd hj)

theorem canonRows_of {d : ℕ} {X : Array W} (hs : X.size = d) (hw : RowsWF X)
    (hz : ZeroFrom 781 X) : canonRows d X = true := by
  unfold canonRows
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨hs, fun i hi => ?_⟩
  have e : X[i] = rowW X i := by unfold rowW; rw [Array.getElem?_eq_getElem hi]; rfl
  rw [e]
  exact W.canon_of_val (hw.row i) (fun j hj => hz i j hj)

theorem zeroFrom_of_canonRows {d : ℕ} {X : Array W} (h : canonRows d X = true) :
    ZeroFrom 781 X := by
  intro i j hj
  by_cases hi : i < X.size
  · have hc : (rowW X i).canon = true := by
      unfold rowW; rw [Array.getElem?_eq_getElem hi]; exact (canonRows_spec h).2 _ (Array.getElem_mem _)
    exact W.canon_val hc hj
  · rw [rowW_ge (by omega), W.val_zero]

theorem eq_of_pw {r : ℕ} {X Y : Array W} (hr : r ≤ 781) (hX : canonRows r X = true)
    (hY : canonRows r Y = true) (h : matW 781 781 X = matW 781 781 Y) : X = Y := by
  refine eq_of_matW_eq hX hY ?_
  ext i j
  have := congrFun (congrFun h ⟨i.val, by omega⟩) j
  rwa [matW_apply, matW_apply] at this ⊢

theorem eqRows_of_pw {r : ℕ} {X Y : Array W} (hr : r ≤ 781) (hX : canonRows r X = true)
    (hY : canonRows r Y = true) (h : matW 781 781 X = matW 781 781 Y) : eqRows r X Y = true := by
  unfold eqRows
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨(canonRows_spec hX).1, eq_of_pw hr hX hY h⟩

theorem eqRows_false_of_pw {r : ℕ} {X Y : Array W}
    (h : matW 781 781 X ≠ matW 781 781 Y) : eqRows r X Y = false := by
  cases hb : eqRows r X Y
  · rfl
  · exact absurd (by rw [(eq_of_eqRows hb).2]) h

theorem pw_mulW {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) (hYs : Y.size ≤ 781) :
    matW 781 781 (mulW X Y) = matW 781 781 X * matW 781 781 Y :=
  matW_mulW (by norm_num) hX hY hYs

theorem zeroFrom_mulW {d : ℕ} {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y)
    (hz : ZeroFrom d Y) : ZeroFrom d (mulW X Y) := by
  intro i k hk
  rw [val_mulW hX hY]
  exact Finset.sum_eq_zero fun j _ => by rw [hz j k hk, mul_zero]

theorem canonRows_mulW' {r : ℕ} {X Y : Array W} (hXs : X.size = r) (hX : RowsWF X)
    (hY : canonRows 781 Y = true) : canonRows r (mulW X Y) = true :=
  canonRows_of (by rw [mulW_size, hXs]) (RowsWF.mulW hX (RowsWF.of_canonRows hY))
    (zeroFrom_mulW hX (RowsWF.of_canonRows hY) (zeroFrom_of_canonRows hY))

theorem pw_addW {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) :
    matW 781 781 (addW 781 X Y) = matW 781 781 X + matW 781 781 Y := matW_addW hX hY

theorem canonRows_addW {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) (hzX : ZeroFrom 781 X)
    (hzY : ZeroFrom 781 Y) : canonRows 781 (addW 781 X Y) = true := by
  refine canonRows_of (addW_size 781 X Y) (RowsWF.addW 781 hX hY) ?_
  intro i j hj
  by_cases hi : i < 781
  · rw [rowW_addW X Y i hi, W.val_add (hX.row i) (hY.row i), hzX i j hj, hzY i j hj, add_zero]
  · rw [rowW_ge (by rw [addW_size]; omega), W.val_zero]

theorem pw_transposeW {R : Array W} (hR : RowsWF R) (hs : R.size = 253) :
    matW 781 781 (transposeW 253 781 R) = (matW 781 781 R).transpose := by
  ext i j
  rw [Matrix.transpose_apply, matW_apply, matW_apply, rowW_transposeW R i.val i.isLt,
    ofTrits_val (by norm_num)]
  by_cases hj : j.val < 253
  · rw [if_pos hj]
    exact tritZ_eq_val (hR.row j.val) i.val
  · rw [if_neg hj, rowW_ge (by omega), W.val_zero]

theorem zeroFrom_transposeW (R : Array W) : ZeroFrom 253 (transposeW 253 781 R) := by
  intro i j hj
  by_cases hi : i < 781
  · rw [rowW_transposeW R i hi, ofTrits_val (by norm_num), if_neg (by omega)]
  · rw [rowW_ge (by rw [transposeW_size]; omega), W.val_zero]

theorem canonRows_transposeW (R : Array W) : canonRows 781 (transposeW 253 781 R) = true :=
  canonRows_of (transposeW_size _ _ _) (RowsWF.transposeW (by norm_num) _ _)
    ((zeroFrom_transposeW R).mono (by norm_num))

@[expose] def pad (A : Matrix (Fin 253) (Fin 253) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  fun i j => if h : i.val < 253 ∧ j.val < 253 then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0

@[expose] def topL (A : Matrix (Fin 781) (Fin 781) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

theorem topL_pad (A : Matrix (Fin 253) (Fin 253) (ZMod 3)) : topL (pad A) = A := by
  ext i j
  unfold topL pad
  rw [dif_pos ⟨i.isLt, j.isLt⟩]

theorem pad_injective {A B : Matrix (Fin 253) (Fin 253) (ZMod 3)} (h : pad A = pad B) : A = B := by
  rw [← topL_pad A, ← topL_pad B, h]

theorem sum_781 (f : Fin 781 → ZMod 3) (hf : ∀ k : Fin 781, 253 ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin 253, f ⟨k.val, by omega⟩ := by
  let g : ℕ → ZMod 3 := fun k => if h : k < 781 then f ⟨k, h⟩ else 0
  have e1 : ∑ k, f k = ∑ k : Fin 781, g k.val := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g, dif_pos k.isLt]
  have e2 : ∑ k : Fin 253, f ⟨k.val, by omega⟩ = ∑ k : Fin 253, g k.val := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g, dif_pos (by omega : k.val < 781)]
  rw [e1, e2, Fin.sum_univ_eq_sum_range g, Fin.sum_univ_eq_sum_range g,
    ← Finset.sum_range_add_sum_Ico _ (by norm_num : 253 ≤ 781)]
  rw [Finset.sum_eq_zero (s := Finset.Ico 253 781) (fun k hk => by
    rw [Finset.mem_Ico] at hk
    simp only [g, dif_pos hk.2]
    exact hf _ hk.1), add_zero]

theorem pad_mul (A B : Matrix (Fin 253) (Fin 253) (ZMod 3)) : pad A * pad B = pad (A * B) := by
  ext i j
  rw [Matrix.mul_apply, sum_781 _ (fun k hk => by unfold pad; rw [dif_neg (by omega), zero_mul])]
  unfold pad
  by_cases hij : i.val < 253 ∧ j.val < 253
  · rw [dif_pos hij, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dif_pos ⟨hij.1, k.isLt⟩, dif_pos ⟨k.isLt, hij.2⟩]
  · rw [dif_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hi : i.val < 253
    · have hj : ¬j.val < 253 := fun h => hij ⟨hi, h⟩
      simp [hj]
    · simp [hi]

theorem pad_one_mul (A : Matrix (Fin 781) (Fin 781) (ZMod 3)) (i j : Fin 781) :
    (pad 1 * A) i j = if i.val < 253 then A i j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · unfold pad
    by_cases hi : i.val < 253
    · rw [dif_pos ⟨hi, hi⟩, if_pos hi, Matrix.one_apply_eq, one_mul]
    · rw [dif_neg (fun h => hi h.1), if_neg hi, zero_mul]
  · intro k _ hk
    unfold pad
    split_ifs with h
    · rw [Matrix.one_apply, if_neg (fun e => hk (Fin.ext (by simpa using (congrArg Fin.val e).symm))),
        zero_mul]
    · rw [zero_mul]
  · simp

theorem mul_pad_one (A : Matrix (Fin 781) (Fin 781) (ZMod 3)) (i j : Fin 781) :
    (A * pad 1) i j = if j.val < 253 then A i j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · unfold pad
    by_cases hj : j.val < 253
    · rw [dif_pos ⟨hj, hj⟩, if_pos hj, Matrix.one_apply_eq, mul_one]
    · rw [dif_neg (fun h => hj h.1), if_neg hj, mul_zero]
  · intro k _ hk
    unfold pad
    split_ifs with h
    · rw [Matrix.one_apply, if_neg (fun e => hk (Fin.ext (by simpa using congrArg Fin.val e))),
        mul_zero]
    · rw [mul_zero]
  · simp

theorem eq_pad_of {A : Matrix (Fin 781) (Fin 781) (ZMod 3)} (h1 : pad 1 * A = A)
    (h2 : A * pad 1 = A) : A = pad (topL A) := by
  ext i j
  unfold pad topL
  by_cases hij : i.val < 253 ∧ j.val < 253
  · rw [dif_pos hij]
  · rw [dif_neg hij]
    by_cases hi : i.val < 253
    · have := congrFun (congrFun h2 i) j
      rw [mul_pad_one, if_neg (fun h => hij ⟨hi, h⟩)] at this
      exact this.symm
    · have := congrFun (congrFun h1 i) j
      rw [pad_one_mul, if_neg hi] at this
      exact this.symm

theorem pw_pad {X : Array W} (hs : X.size = 253) (hz : ZeroFrom 253 X) :
    matW 781 781 X = pad (matW 253 253 X) := by
  ext i j
  unfold pad
  rw [matW_apply]
  by_cases hij : i.val < 253 ∧ j.val < 253
  · rw [dif_pos hij, matW_apply]
  · rw [dif_neg hij]
    by_cases hi : i.val < 253
    · exact hz i j (by omega)
    · rw [rowW_ge (by omega), W.val_zero]

theorem zeroFrom_idW253 : ZeroFrom 253 (idW 253) := by
  intro i j hj
  by_cases hi : i < 253
  · rw [rowW_idW i hi, W.val_setTrit (by omega) (W.val_zero _), if_neg (by omega), W.val_zero]
  · rw [rowW_ge (by rw [idW_size]; omega), W.val_zero]

theorem canonRows_idW253 : canonRows 253 (idW 253) = true :=
  canonRows_of (idW_size 253) (RowsWF.idW (by norm_num)) (zeroFrom_idW253.mono (by norm_num))

theorem pw_idW253 : matW 781 781 (idW 253) = pad 1 := by
  rw [pw_pad (idW_size 253) zeroFrom_idW253, matW_idW (by norm_num)]

theorem invW253_spec {M : Array W} (hs : M.size = 253) (hw : RowsWF M) (hz : ZeroFrom 253 M)
    {N : Matrix (Fin 781) (Fin 781) (ZMod 3)} (hNM : N * matW 781 781 M = pad 1)
    (h1 : pad 1 * N = N) (h2 : N * pad 1 = N) :
    canonRows 253 (invW 253 M) = true ∧ ZeroFrom 253 (invW 253 M) ∧
      matW 781 781 (invW 253 M) = N := by
  have hN := eq_pad_of h1 h2
  have hM := pw_pad hs hz
  have hT : topL N * matW 253 253 M = 1 := by
    apply pad_injective
    rw [← pad_mul, ← hN, ← hM, hNM]
  have hdet : (matW 253 253 M).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hT
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨hs', hw', hz', hinv⟩ := invW_spec (by norm_num) hs hw hdet
  have hz2 : ZeroFrom 253 (invW 253 M) := hz'
  refine ⟨canonRows_of hs' hw' (hz2.mono (by norm_num)), hz2, ?_⟩
  rw [pw_pad hs' hz2, hN]
  refine congrArg pad ?_
  have hu : IsUnit (matW 253 253 M).det := isUnit_iff_ne_zero.2 hdet
  have hl : ∀ Y : Matrix (Fin 253) (Fin 253) (ZMod 3), Y * matW 253 253 M = 1 →
      Y = (matW 253 253 M)⁻¹ := by
    intro Y hY
    rw [← Matrix.mul_one Y, ← Matrix.mul_nonsing_inv _ hu, ← Matrix.mul_assoc, hY, Matrix.one_mul]
  rw [hl _ hinv, hl _ hT]

theorem invW781_spec {M : Array W} (hM : canonRows 781 M = true)
    {N : Matrix (Fin 781) (Fin 781) (ZMod 3)} (hMN : matW 781 781 M * N = 1) :
    canonRows 781 (invW 781 M) = true ∧ matW 781 781 (invW 781 M) = N := by
  have hdet : (matW 781 781 M).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMN
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨hs', hw', hz', hinv⟩ := invW_spec (le_refl 781) (canonRows_spec hM).1
    (RowsWF.of_canonRows hM) hdet
  refine ⟨canonRows_of hs' hw' hz', ?_⟩
  calc matW 781 781 (invW 781 M) = matW 781 781 (invW 781 M) * (matW 781 781 M * N) := by
        rw [hMN, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

theorem rowsWF_rowsOfSeed' (d : ℕ) (hd : d ≤ 781) (s : String) : RowsWF (rowsOfSeed d s) := by
  intro x hx
  unfold rowsOfSeed at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf (by omega) _

theorem rowsOfSeed_size' (d : ℕ) (s : String) : (rowsOfSeed d s).size = d := by
  unfold rowsOfSeed; simp

theorem zeroFrom_rowsOfSeed (d : ℕ) (hd : d ≤ 781) (s : String) : ZeroFrom d (rowsOfSeed d s) := by
  intro i j hj
  by_cases hi : i < d
  · unfold rowsOfSeed
    rw [rowW_ofFn, dif_pos hi, ofTrits_val (by omega), if_neg (by omega)]
  · rw [rowW_ge (by rw [rowsOfSeed_size']; omega), W.val_zero]

theorem canonRows_rowsOfSeed (d : ℕ) (hd : d ≤ 781) (s : String) :
    canonRows d (rowsOfSeed d s) = true :=
  canonRows_of (rowsOfSeed_size' d s) (rowsWF_rowsOfSeed' d hd s)
    ((zeroFrom_rowsOfSeed d hd s).mono hd)

theorem matW_rowsOfSeed' (d : ℕ) (hd : d ≤ 781) (s : String) :
    matW d d (rowsOfSeed d s) = Blueprint.NativeSporadic.decode 3 d 1 s := by
  ext i j
  unfold rowsOfSeed
  rw [matW_apply, rowW_ofFn, dif_pos i.isLt, ofTrits_val (by omega), if_pos j.isLt,
    CFSG.F3.Native.decode_apply_eq_decodeEntries, List.getElem?_toArray]

theorem rowW_ofFn_ofTrits_val {n d m : ℕ} (hd : d ≤ 832) (e : Array ℕ) {i j : ℕ} (hi : i < n) :
    (rowW (Array.ofFn (n := n) fun i => ofTrits d fun j => e[m * i.val + j]?.getD 0) i).val j =
      if j < d then ((e[m * i + j]?.getD 0 : ℕ) : ZMod 3) else 0 := by
  unfold rowW
  rw [Array.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]
  rw [ofTrits_val hd]

theorem rowW_matF_val {i j : ℕ} (hi : i < 781) (hj : j < 781) :
    (rowW (matF ()) i).val j = (((decode81 formData)[781 * i + j]?.getD 0 : ℕ) : ZMod 3) :=
  (rowW_ofFn_ofTrits_val (n := 781) (d := 781) (m := 781) (by norm_num) (decode81 formData)
    hi).trans (if_pos hj)

theorem rowsWF_matF : RowsWF (matF ()) := by
  intro x hx
  unfold matF at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf (by norm_num) _

theorem matF_size : (matF ()).size = 781 := by unfold matF; simp

theorem rowW_basisRows_val {i j : ℕ} (hi : i < 253) :
    (rowW (basisRows ()) i).val j =
      if j < 253 then (((decode81 basisData)[253 * i + j]?.getD 0 : ℕ) : ZMod 3) else 0 :=
  rowW_ofFn_ofTrits_val (n := 253) (d := 253) (m := 253) (by norm_num) (decode81 basisData) hi

theorem rowsWF_basisRows : RowsWF (basisRows ()) := by
  intro x hx
  unfold basisRows at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf (by norm_num) _

theorem basisRows_size : (basisRows ()).size = 253 := by unfold basisRows; simp

theorem zeroFrom_basisRows : ZeroFrom 253 (basisRows ()) := by
  intro i j hj
  by_cases hi : i < 253
  · rw [rowW_basisRows_val hi, if_neg (by omega)]
  · rw [rowW_ge (by rw [basisRows_size]; omega), W.val_zero]

theorem zeroFrom_initRows_rows (i : ℕ) (hi : 253 ≤ i) (j : ℕ) : (rowW (initRows ()) i).val j = 0 := by
  rw [rowW_ge (by rw [CFSG.KC.Fi24FixS.initRows_size]; exact hi), W.val_zero]

theorem bitP_of_val_one {x : W} (hx : x.wf = true) {c : ℕ} (h : x.val c = 1) : x.bitP c = true := by
  have hne : x.val c ≠ 0 := by rw [h]; decide
  have hb := (val_ne_zero_iff hx c).1 hne
  rw [Bool.or_eq_true] at hb
  rcases hb with h1 | h1
  · exact h1
  · rw [val_eq_two_of_bitM hx h1] at h; exact absurd h (by decide)

theorem bitM_of_val_one {x : W} (hx : x.wf = true) {c : ℕ} (h : x.val c = 1) :
    x.bitM c = false := by
  cases h2 : x.bitM c
  · rfl
  · rw [val_eq_two_of_bitM hx h2] at h; exact absurd h (by decide)

theorem bits_of_val_zero {x : W} (hx : x.wf = true) {c : ℕ} (h : x.val c = 0) :
    x.bitP c = false ∧ x.bitM c = false := by
  have := mt (val_ne_zero_iff hx c).2 (not_not.2 h)
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at this
  exact this

theorem swapIfInBounds_self (X : Array W) (c : ℕ) : X.swapIfInBounds c c = X := by
  apply Array.ext (by simp)
  intro k h1 h2
  rw [Array.getElem_swapIfInBounds]
  split_ifs <;> simp_all

theorem initRows_val {i j : ℕ} (hi : i < 253) (hj : j < 253) :
    (rowW (initRows ()) i).val j = if j = i then 1 else 0 := by
  rw [CFSG.KC.Fi24FixS.rowW_initRows_val hi (by omega), if_pos hj]
  split_ifs <;> rfl

theorem colStep_unit {X : Array W} {r : ℕ} (hs : X.size = r) (hw : RowsWF X)
    (hu : ∀ i < r, ∀ j < r, (rowW X i).val j = if j = i then 1 else 0) (c : ℕ) (hc : c < r)
    (piv : Array ℕ) : ∃ piv', colStep ⟨X, c, piv⟩ c = ⟨X, c + 1, piv'⟩ := by
  have hcs : c < X.size := by rw [hs]; exact hc
  have hcc : (rowW X c).val c = 1 := by rw [hu c hc c hc, if_pos rfl]
  have e : ∀ h (hx : h < X.size), X[h] = rowW X h := by
    intro h hx; unfold rowW; rw [Array.getElem?_eq_getElem hx, Option.getD_some]
  have hpiv : findPiv X (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64) c = c := by
    unfold findPiv
    rw [dif_pos hcs, e c hcs, nz_bit, bitP_of_val_one (hw.row c) hcc, Bool.true_or, if_pos rfl]
  have h1 : (⟨X, c, piv⟩ : RRef).rank < (⟨X, c, piv⟩ : RRef).rows.size := hcs
  unfold colStep
  rw [if_pos h1]
  change ∃ piv', (if findPiv X (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64) c <
      X.size then _ else _) = _
  rw [hpiv, if_pos hcs]
  dsimp only
  rw [swapIfInBounds_self]
  have e2 : (X[c]?.getD W.zero) = rowW X c := rfl
  rw [e2, limbM_bit, bitM_of_val_one (hw.row c) hcc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hel : elimRows X c (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64) (rowW X c) = X := by
    apply Array.ext (by rw [elimRows_size])
    intro h hh hh'
    have e5 : ∀ (Y : Array W) (hy : h < Y.size), Y[h] = rowW Y h := by
      intro Y hy; unfold rowW; rw [Array.getElem?_eq_getElem hy, Option.getD_some]
    rw [e5 _ hh, e5 _ hh', rowW_elimRows _ _ _ _ _ _ hh']
    by_cases hhc : h = c
    · rw [if_pos hhc]
    · rw [if_neg hhc]
      have h0 : (rowW X h).val c = 0 := by
        rw [hu h (by rw [hs] at hh'; exact hh') c hc, if_neg (Ne.symm hhc)]
      obtain ⟨b1, b2⟩ := bits_of_val_zero (hw.row h) h0
      rw [limbP_bit, limbM_bit, b1, b2]
      simp
  have hel' : elimRows X c (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64)
      (X[c]?.getD W.zero) = X := hel
  rw [hel']
  exact ⟨_, rfl⟩

theorem colStep_full (st : RRef) (h : st.rows.size ≤ st.rank) (c : ℕ) : colStep st c = st := by
  unfold colStep
  rw [if_neg (by omega)]

theorem rref_unit {X : Array W} {r : ℕ} (hs : X.size = r) (hw : RowsWF X)
    (hu : ∀ i < r, ∀ j < r, (rowW X i).val j = if j = i then 1 else 0) (d : ℕ) :
    (rref d X).rows = X := by
  have key : ∀ n, n ≤ d → ∃ piv, Nat.fold n (fun c _ st => colStep st c)
      (⟨X, 0, #[]⟩ : RRef) = ⟨X, min n r, piv⟩ := by
    intro n hn
    induction n with
    | zero => exact ⟨#[], by rw [Nat.fold_zero]; rfl⟩
    | succ n ih =>
      obtain ⟨piv, hp⟩ := ih (by omega)
      rw [Nat.fold_succ, hp]
      by_cases h : n < r
      · obtain ⟨piv', hp'⟩ := colStep_unit hs hw hu n h piv
        rw [Nat.min_eq_left (by omega)]
        rw [Nat.min_eq_left (by omega)] at hp ⊢
        exact ⟨piv', hp'⟩
      · refine ⟨piv, ?_⟩
        rw [colStep_full _ (by simp [hs]; omega)]
        congr 1
        omega
  obtain ⟨piv, hp⟩ := key d le_rfl
  unfold rref
  rw [hp]

theorem rootForm_rows : (rootForm ()).rows = initRows () := by
  unfold rootForm
  exact rref_unit CFSG.KC.Fi24FixS.initRows_size CFSG.KC.Fi24FixS.rowsWF_initRows
    (fun i hi j hj => initRows_val hi hj) 781

end CFSG.Sporadic.Fi24.Native
