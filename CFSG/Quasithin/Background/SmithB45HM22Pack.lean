module

public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.CharacterTheory.SteinbergBYNortonCriterion
public import Mathlib.Data.List.GetD

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY Matrix

abbrev PV : Type := ℕ × ℕ

namespace PV

@[expose] def get (v : PV) (i : ℕ) : FieldFour := ⟨v.1.testBit i, v.2.testBit i⟩

@[expose] def add (u v : PV) : PV := (u.1 ^^^ v.1, u.2 ^^^ v.2)

@[expose] def smul (c : FieldFour) (v : PV) : PV :=
  ((bif c.re then v.1 else 0) ^^^ (bif c.im then v.2 else 0),
    (bif c.re then v.2 else 0) ^^^ (bif c.im then v.1 ^^^ v.2 else 0))

@[expose] def frob (v : PV) : PV := (v.1 ^^^ v.2, v.2)

@[expose] def shr (v : PV) (n : ℕ) : PV := (v.1 >>> n, v.2 >>> n)

@[expose] def trunc (v : PV) (m : ℕ) : PV := (v.1 % 2 ^ m, v.2 % 2 ^ m)

@[expose] def shl (v : PV) (n : ℕ) : PV := (v.1 <<< n, v.2 <<< n)

@[expose] def eqv (m : ℕ) (u v : PV) : Bool :=
  u.1 % 2 ^ m == v.1 % 2 ^ m && u.2 % 2 ^ m == v.2 % 2 ^ m

@[expose] def lowZero (n : ℕ) (v : PV) : Bool := v.1 >>> n == 0 && v.2 >>> n == 0

@[expose] def single (j : ℕ) (c : FieldFour) : PV :=
  (bif c.re then 2 ^ j else 0, bif c.im then 2 ^ j else 0)

@[expose] def toVec (n : ℕ) (v : PV) : Fin n → FieldFour := fun i => v.get i

theorem get_zero (i : ℕ) : get (0, 0) i = 0 := by
  simp only [get, Nat.zero_testBit]
  rfl

theorem get_add (u v : PV) (i : ℕ) : (add u v).get i = u.get i + v.get i := by
  simp only [get, add, Nat.testBit_xor]
  rfl

theorem testBit_cond (b : Bool) (x i : ℕ) :
    (bif b then x else 0).testBit i = (b && x.testBit i) := by
  cases b <;> simp

theorem get_smul (c : FieldFour) (v : PV) (i : ℕ) : (smul c v).get i = c * v.get i := by
  obtain ⟨r, s⟩ := c
  simp only [get, smul, Nat.testBit_xor, testBit_cond]
  apply FieldFour.ext
  · change _ = xor (r && v.1.testBit i) (s && v.2.testBit i)
    rfl
  · change _ = xor (xor (r && v.2.testBit i) (s && v.1.testBit i)) (s && v.2.testBit i)
    cases r <;> cases s <;> cases v.1.testBit i <;> cases v.2.testBit i <;> rfl

theorem get_single (j : ℕ) (c : FieldFour) (i : ℕ) :
    (single j c).get i = if i = j then c else 0 := by
  obtain ⟨r, s⟩ := c
  simp only [get, single, testBit_cond, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']
    rfl

theorem get_foldr_add {α : Type*} (l : List α) (f : α → PV) (i : ℕ) :
    (l.foldr (fun x acc => add (f x) acc) (0, 0)).get i = (l.map fun x => (f x).get i).sum := by
  induction l with
  | nil => simp [get_zero]
  | cons a l ih => rw [List.foldr_cons, get_add, ih, List.map_cons, List.sum_cons]

theorem get_frob (v : PV) (i : ℕ) : (frob v).get i = FieldFour.frob (v.get i) := by
  simp only [get, frob, Nat.testBit_xor]
  rfl

theorem get_shr (v : PV) (n i : ℕ) : (shr v n).get i = v.get (n + i) := by
  simp only [get, shr, Nat.testBit_shiftRight]

theorem get_trunc (v : PV) (m i : ℕ) : (trunc v m).get i = if i < m then v.get i else 0 := by
  simp only [get, trunc, Nat.testBit_mod_two_pow]
  split_ifs with h
  · simp [h]
  · simp [h]
    rfl

theorem get_shl (v : PV) (n i : ℕ) :
    (shl v n).get i = if n ≤ i then v.get (i - n) else 0 := by
  simp only [get, shl, Nat.testBit_shiftLeft]
  split_ifs with h
  · simp [h]
  · simp [h]
    rfl

theorem get_eq_of_eqv {m : ℕ} {u v : PV} (h : eqv m u v = true) {i : ℕ} (hi : i < m) :
    u.get i = v.get i := by
  simp only [eqv, Bool.and_eq_true, beq_iff_eq] at h
  have h1 := congrArg (fun x => Nat.testBit x i) h.1
  have h2 := congrArg (fun x => Nat.testBit x i) h.2
  simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and] at h1 h2
  simp only [get, h1, h2]

theorem toVec_eq_of_eqv {m : ℕ} {u v : PV} (h : eqv m u v = true) : toVec m u = toVec m v :=
  funext fun i => get_eq_of_eqv h i.isLt

theorem get_eq_zero_of_lowZero {n : ℕ} {v : PV} (h : lowZero n v = true) {i : ℕ} (hi : n ≤ i) :
    v.get i = 0 := by
  simp only [lowZero, Bool.and_eq_true, beq_iff_eq] at h
  have h1 := congrArg (fun x => Nat.testBit x (i - n)) h.1
  have h2 := congrArg (fun x => Nat.testBit x (i - n)) h.2
  simp only [Nat.testBit_shiftRight, Nat.add_sub_cancel' hi, Nat.zero_testBit] at h1 h2
  simp only [get, h1, h2]
  rfl

end PV

abbrev PM : Type := List PV

namespace PM

open PV

@[expose] def mulVec : PM → PV → PV
  | [], _ => (0, 0)
  | c :: cs, x => PV.add (PV.smul (x.get 0) c) (mulVec cs (x.shr 1))

@[expose] def mul (M N : PM) : PM := N.map (mulVec M)

@[expose] def idm (n : ℕ) : PM := (List.range n).map fun j => PV.single j 1

@[expose] def eqm (m : ℕ) (M N : PM) : Bool :=
  M.length == N.length && (M.zip N).all fun p => PV.eqv m p.1 p.2

@[expose] def frob (M : PM) : PM := M.map PV.frob

@[expose] def col (M : PM) (j : ℕ) : PV := M.getD j (0, 0)

@[expose] def toMat (m n : ℕ) (M : PM) : Matrix (Fin m) (Fin n) FieldFour :=
  fun i j => (col M j).get i

@[expose] def row (M : PM) (i : ℕ) : PV :=
  (List.range M.length).foldr (fun j acc => PV.add (PV.single j ((col M j).get i)) acc) (0, 0)

@[expose] def transp (m : ℕ) (M : PM) : PM := (List.range m).map (row M)

@[expose] def kronCol (dA dB : ℕ) (a b : PV) : PV :=
  (List.range dA).foldr (fun i acc => PV.add (PV.shl (PV.smul (a.get i) (b.trunc dB)) (dB * i)) acc)
    (0, 0)

@[expose] def kron (dA dB : ℕ) (A B : PM) : PM :=
  A.flatMap fun a => B.map fun b => kronCol dA dB a b

@[expose] def unpack (m n : ℕ) (M : PM) : Vector (Vector FieldFour n) m :=
  Vector.ofFn fun i => Vector.ofFn fun j => (col M j).get i

theorem col_cons_zero (c : PV) (cs : PM) : col (c :: cs) 0 = c := rfl

theorem col_cons_succ (c : PV) (cs : PM) (j : ℕ) : col (c :: cs) (j + 1) = col cs j := rfl

theorem col_ge {M : PM} {j : ℕ} (h : M.length ≤ j) : col M j = (0, 0) := by
  simp only [col]
  rw [List.getD_eq_default _ _ h]

theorem get_mulVec (M : PM) (x : PV) (i : ℕ) :
    (mulVec M x).get i = ∑ j : Fin M.length, x.get j * (col M j).get i := by
  induction M generalizing x with
  | nil => simp [mulVec, PV.get_zero]
  | cons c cs ih =>
    rw [mulVec, PV.get_add, PV.get_smul, ih, List.length_cons, Fin.sum_univ_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PV.get_shr, Fin.val_succ, Nat.add_comm 1, col_cons_succ]

theorem toVec_mulVec {m n : ℕ} (M : PM) (hM : M.length = n) (x : PV) :
    PV.toVec m (mulVec M x) = toMat m n M *ᵥ PV.toVec n x := by
  subst hM
  funext i
  rw [PV.toVec, get_mulVec, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

theorem length_mul (M N : PM) : (mul M N).length = N.length := List.length_map _

theorem col_mul (M N : PM) (j : ℕ) (hj : j < N.length) : col (mul M N) j = mulVec M (col N j) := by
  simp only [col, mul]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj,
    List.getElem_map]

theorem toMat_mul {m n p : ℕ} (M N : PM) (hM : M.length = n) (hN : N.length = p) :
    toMat m p (mul M N) = toMat m n M * toMat n p N := by
  funext i j
  have hj : (j : ℕ) < N.length := hN ▸ j.isLt
  have h := congrFun (toVec_mulVec (m := m) M hM (col N j)) i
  simp only [PV.toVec] at h
  rw [toMat, col_mul M N j hj, h, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rfl

theorem toMat_idm (n : ℕ) : toMat n n (idm n) = 1 := by
  funext i j
  simp only [toMat, col, idm]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, PV.get_single,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem toMat_eq_of_eqm {m n : ℕ} {M N : PM} (h : eqm m M N = true) :
    toMat m n M = toMat m n N := by
  simp only [eqm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  funext i j
  simp only [toMat, col]
  by_cases hj : (j : ℕ) < M.length
  · have hj' : (j : ℕ) < N.length := hlen ▸ hj
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']
    have hmem : (M[(j : ℕ)], N[(j : ℕ)]) ∈ M.zip N := by
      rw [List.mem_iff_getElem]
      exact ⟨j, by simp [hj, hj'], by simp⟩
    exact PV.get_eq_of_eqv (hall _ hmem) i.isLt
  · have hj' : ¬ (j : ℕ) < N.length := hlen ▸ hj
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem col_frob (M : PM) (j : ℕ) : col (frob M) j = if j < M.length then (col M j).frob
    else (0, 0) := by
  simp only [col, frob]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h,
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using h)]

theorem toMat_frob {m n : ℕ} (M : PM) (hM : M.length = n) :
    toMat m n (frob M) = (toMat m n M).map FieldFour.frob := by
  funext i j
  simp only [toMat, Matrix.map_apply, col_frob, hM, j.isLt, ite_true, PV.get_frob]

theorem sum_range_ite_eq {n j : ℕ} (hj : j < n) (f : ℕ → FieldFour) :
    ((List.range n).map fun k => if j = k then f k else 0).sum = f j := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
    Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 hj)]

theorem get_row (M : PM) (i j : ℕ) (hj : j < M.length) : (row M i).get j = (col M j).get i := by
  rw [row, PV.get_foldr_add]
  simp only [PV.get_single]
  exact sum_range_ite_eq hj _

theorem length_transp (m : ℕ) (M : PM) : (transp m M).length = m := by simp [transp]

theorem toMat_transp {m n : ℕ} (M : PM) (hM : M.length = n) :
    toMat n m (transp m M) = (toMat m n M).transpose := by
  funext j i
  simp only [toMat, Matrix.transpose_apply, col, transp]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  exact get_row M i j (hM ▸ j.isLt)

theorem get_kronCol (dA dB : ℕ) (a b : PV) (i₁ i₂ : ℕ) (h₁ : i₁ < dA) (h₂ : i₂ < dB) :
    (kronCol dA dB a b).get (dB * i₁ + i₂) = a.get i₁ * b.get i₂ := by
  rw [kronCol, PV.get_foldr_add]
  have hterm : ∀ i, (PV.shl (PV.smul (a.get i) (b.trunc dB)) (dB * i)).get (dB * i₁ + i₂) =
      if i₁ = i then a.get i₁ * b.get i₂ else 0 := by
    intro i
    rw [PV.get_shl]
    by_cases hii : i₁ = i
    · subst hii
      rw [ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left, PV.get_smul, PV.get_trunc,
        ite_eq_left h₂, ite_eq_left rfl]
    · rw [ite_eq_right hii]
      split_ifs with hle
      · rw [PV.get_smul, PV.get_trunc]
        have hlt2 : ¬ dB * i₁ + i₂ - dB * i < dB := by
          intro hcon
          rcases Nat.lt_or_gt_of_ne hii with hlt' | hgt
          · have : dB * (i₁ + 1) ≤ dB * i := Nat.mul_le_mul_left _ hlt'
            rw [Nat.mul_succ] at this
            omega
          · have : dB * (i + 1) ≤ dB * i₁ := Nat.mul_le_mul_left _ hgt
            rw [Nat.mul_succ] at this
            omega
        rw [ite_eq_right hlt2, mul_zero]
      · rfl
  simp only [hterm]
  exact sum_range_ite_eq h₁ (fun _ => a.get i₁ * b.get i₂)

theorem col_kron (dA dB : ℕ) (A B : PM) (j₁ j₂ : ℕ) (h₁ : j₁ < A.length) (h₂ : j₂ < B.length) :
    col (kron dA dB A B) (B.length * j₁ + j₂) = kronCol dA dB (col A j₁) (col B j₂) := by
  induction A generalizing j₁ with
  | nil => simp at h₁
  | cons a A ih =>
    simp only [kron, List.flatMap_cons] at ih ⊢
    rcases j₁ with _ | j₁
    · simp only [col, Nat.mul_zero, Nat.zero_add]
      rw [List.getD_append _ _ _ _ (by simpa using h₂),
        List.getD_eq_getElem _ _ (by simpa using h₂),
        List.getElem_map, List.getD_eq_getElem _ _ h₂, List.getD_cons_zero]
    · have h₁' : j₁ < A.length := by simpa using h₁
      have e : B.length * (j₁ + 1) + j₂ = B.length + (B.length * j₁ + j₂) := by ring
      simp only [col] at ih ⊢
      rw [e, List.getD_append_right _ _ _ _ (by simp), List.length_map, Nat.add_sub_cancel_left,
        ih j₁ h₁', List.getD_cons_succ]

theorem length_kron (dA dB : ℕ) (A B : PM) : (kron dA dB A B).length = A.length * B.length := by
  induction A with
  | nil => simp [kron]
  | cons a A ih =>
    simp only [kron, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

open scoped Kronecker in
theorem toMat_kron {dA dB nA nB : ℕ} (A B : PM) (hA : A.length = nA) (hB : B.length = nB) :
    toMat (dA * dB) (nA * nB) (kron dA dB A B) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (toMat dA nA A ⊗ₖ toMat dB nB B) := by
  funext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, toMat]
  have hcol : ((finProdFinEquiv (j₁, j₂) : Fin (nA * nB)) : ℕ) = B.length * j₁ + j₂ := by
    simp [finProdFinEquiv, hB, Nat.add_comm]
  have hrow : ((finProdFinEquiv (i₁, i₂) : Fin (dA * dB)) : ℕ) = dB * i₁ + i₂ := by
    simp [finProdFinEquiv, Nat.add_comm]
  rw [hcol, hrow, col_kron dA dB A B j₁ j₂ (hA ▸ j₁.isLt) (hB ▸ j₂.isLt),
    get_kronCol dA dB _ _ i₁ i₂ i₁.isLt i₂.isLt]

theorem untab_unpack (m n : ℕ) (M : PM) : untab (unpack m n M) = toMat m n M := by
  funext i j
  simp [untab, unpack, toMat]

@[expose] def trace (n : ℕ) (M : PM) : FieldFour :=
  ((List.range n).map fun i => (col M i).get i).sum

theorem trace_eq (n : ℕ) (M : PM) : trace n M = Matrix.trace (toMat n n M) := by
  rw [trace, Matrix.trace, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
    ← Fin.sum_univ_eq_sum_range]
  rfl

end PM

end CFSG.Quasithin.HM22
