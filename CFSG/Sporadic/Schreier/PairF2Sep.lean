module

public import CFSG.Sporadic.Schreier.PairF2Quad

public section

namespace CFSG.Sporadic.Schreier.PairF2

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

@[expose] def zeroRows (d : ℕ) : Array ℕ := Array.replicate d 0

@[expose] def prodRows (d : ℕ) (mats : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldl (fun M x => mulRows d M mats[x]!) (idRows d)

@[expose] def combRows (d : ℕ) (mats : Array (Array ℕ)) (terms : List (List ℕ)) : Array ℕ :=
  terms.foldl (fun acc w => addRows acc (prodRows d mats w)) (zeroRows d)

@[expose] def mulVecRows (d : ℕ) (M : Array ℕ) (v : ℕ) : ℕ := vecMulN d (transposeRows d M) v

@[expose] def projRows (d v k : ℕ) : Array ℕ :=
  Array.ofFn (n := d) fun i => (1 <<< i.val) ^^^ (if v.testBit i.val then 1 <<< k else 0)

@[expose] def spinVecs (d : ℕ) (mats : Array (Array ℕ)) (v : ℕ) (tree : List (ℕ × ℕ)) :
    Array ℕ :=
  tree.foldl (fun S t => S.push (mulVecRows d mats[t.2]! S[t.1]!)) #[v]

@[expose] def invRowsF2 (d : ℕ) (M : Array ℕ) : Array ℕ := Id.run do
  let mut a := M
  let mut r := idRows d
  for c in [0:d] do
    let mut piv := d
    for i in [c:d] do
      if piv == d && (a[i]!).testBit c then piv := i
    if piv < d then
      let ap := a[piv]!
      let rp := r[piv]!
      a := (a.set! piv a[c]!).set! c ap
      r := (r.set! piv r[c]!).set! c rp
      for i in [0:d] do
        if i != c && (a[i]!).testBit c then
          a := a.set! i (a[i]! ^^^ ap)
          r := r.set! i (r[i]! ^^^ rp)
  return r

@[expose] def sepF2OK (d : ℕ) (mats : Array (Array ℕ)) (terms : List (List ℕ)) (v k : ℕ)
    (P Tinv : Array ℕ) (tree : List (ℕ × ℕ)) (S : Array ℕ) : Bool :=
  decide (k < d) && v.testBit k && mats.all (fun M => M.size == d) &&
    mulVecRows d (combRows d mats terms) v == 0 && P.size == d &&
    mulRows d P (combRows d mats terms) == projRows d v k &&
    S.size == tree.length + 1 && S[0]! == v &&
    (List.range tree.length).all (fun i => decide (tree[i]!.1 ≤ i) &&
      decide (tree[i]!.2 < mats.size) &&
        S[i + 1]! == mulVecRows d mats[tree[i]!.2]! S[tree[i]!.1]!) &&
    S.size == d && Tinv.size == d && mulRows d Tinv S == idRows d

variable {d : ℕ}

theorem size_mulRows (X Y : Array ℕ) : (mulRows d X Y).size = X.size := by
  simp [mulRows]

theorem size_prodRows (mats : Array (Array ℕ)) (w : List ℕ) : (prodRows d mats w).size = d := by
  unfold prodRows
  suffices h : ∀ (M : Array ℕ), M.size = d → (w.foldl (fun M x => mulRows d M mats[x]!) M).size = d
    from h _ (by simp [idRows])
  induction w with
  | nil => intro M hM; exact hM
  | cons x w ih =>
    intro M hM
    rw [List.foldl_cons]
    exact ih _ (by rw [size_mulRows, hM])

theorem rowsMatrix_prodRows (mats : Array (Array ℕ)) (w : List ℕ) :
    rowsMatrix d (prodRows d mats w) = (w.map fun x => rowsMatrix d mats[x]!).prod := by
  unfold prodRows
  suffices h : ∀ M : Array ℕ, rowsMatrix d (w.foldl (fun M x => mulRows d M mats[x]!) M) =
      rowsMatrix d M * (w.map fun x => rowsMatrix d mats[x]!).prod by
    rw [h, rowsMatrix_idRows, one_mul]
  induction w with
  | nil => intro M; simp
  | cons x w ih =>
    intro M
    rw [List.foldl_cons, ih, rowsMatrix_mulRows, List.map_cons, List.prod_cons, mul_assoc]

theorem rowsMatrix_zeroRows : rowsMatrix d (zeroRows d) = 0 := by
  ext i j
  rw [rowsMatrix_apply, zeroRows, Array.getElem?_replicate, ite_eq_left i.2, Option.getD_some,
    toVecD_zero]
  rfl

theorem rowsMatrix_combRows (mats : Array (Array ℕ)) (terms : List (List ℕ)) :
    rowsMatrix d (combRows d mats terms) =
      (terms.map fun w => rowsMatrix d (prodRows d mats w)).sum := by
  unfold combRows
  suffices h : ∀ acc : Array ℕ, acc.size = d →
      rowsMatrix d (terms.foldl (fun acc w => addRows acc (prodRows d mats w)) acc) =
        rowsMatrix d acc + (terms.map fun w => rowsMatrix d (prodRows d mats w)).sum by
    rw [h _ (by simp [zeroRows]), rowsMatrix_zeroRows, zero_add]
  induction terms with
  | nil => intro acc _; simp
  | cons w terms ih =>
    intro acc hacc
    rw [List.foldl_cons, ih _ (by simp [addRows, hacc, size_prodRows]),
      rowsMatrix_addRows hacc (size_prodRows mats w), List.map_cons, List.sum_cons, add_assoc]

theorem toVecD_mulVecRows (M : Array ℕ) (v : ℕ) :
    toVecD d (mulVecRows d M v) = rowsMatrix d M *ᵥ toVecD d v :=
  (rowsMatrix_mulVec d M v).symm

theorem rowsMatrix_projRows (v k : ℕ) (hk : k < d) :
    rowsMatrix d (projRows d v k) = 1 + vecMulVec (toVecD d v) (Pi.single ⟨k, hk⟩ 1) := by
  ext i j
  rw [rowsMatrix_apply, projRows, Array.getElem?_ofFn, dite_eq_left i.2, Option.getD_some,
    toVecD_xor, Pi.add_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
  congr 1
  · rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
      simp [h, h']
  · rw [toVecD_apply d v i, Pi.single_apply]
    by_cases hv : v.testBit i
    · simp only [hv, ite_true, toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, one_mul]
      by_cases hj : j = ⟨k, hk⟩
      · subst hj; simp
      · have hj' : k ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [hj, hj']
    · simp [hv, toVecD_zero]

theorem commute_prod {mats : Array (Array ℕ)} {g : Matrix (Fin d) (Fin d) (ZMod 2)}
    (hg : ∀ i < mats.size, g * rowsMatrix d mats[i]! = rowsMatrix d mats[i]! * g) :
    ∀ w : List ℕ, (∀ x ∈ w, x < mats.size) →
      g * (w.map fun x => rowsMatrix d mats[x]!).prod =
        (w.map fun x => rowsMatrix d mats[x]!).prod * g
  | [], _ => by simp
  | x :: w, hw => by
    rw [List.map_cons, List.prod_cons, ← mul_assoc, hg x (hw x List.mem_cons_self), mul_assoc,
      commute_prod hg w (fun y hy => hw y (List.mem_cons_of_mem x hy)), mul_assoc]

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem eq_zero_or_one_of_sepF2OK {mats : Array (Array ℕ)} {terms : List (List ℕ)} {v k : ℕ}
    {P Tinv : Array ℕ} {tree : List (ℕ × ℕ)} {S : Array ℕ}
    (h : sepF2OK d mats terms v k P Tinv tree S = true)
    (hterms : ∀ w ∈ terms, ∀ x ∈ w, x < mats.size) (g : Matrix (Fin d) (Fin d) (ZMod 2))
    (hg : ∀ i < mats.size, g * rowsMatrix d mats[i]! = rowsMatrix d mats[i]! * g) :
    g = 0 ∨ g = 1 := by
  unfold sepF2OK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hvk⟩, -⟩, hKv⟩, hPs⟩, hPK⟩, hSlen⟩, hS0⟩, hspin⟩, hSd⟩, -⟩, hTS⟩ := h
  set K := rowsMatrix d (combRows d mats terms) with hKdef
  set x := toVecD d v with hx
  have hgK : g * K = K * g := by
    rw [hKdef, rowsMatrix_combRows]
    refine (Commute.list_sum_right _ _ fun M hM => ?_).eq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hM
    rw [rowsMatrix_prodRows]
    exact commute_prod hg w (hterms w hw)
  have hKx : K *ᵥ x = 0 := by
    rw [hx, ← toVecD_mulVecRows, hKv, toVecD_zero]
  have hker : ∀ y : Fin d → ZMod 2, K *ᵥ y = 0 → y = y ⟨k, hk⟩ • x := by
    intro y hy
    have h1 : (rowsMatrix d P * K) *ᵥ y = 0 := by rw [← mulVec_mulVec, hy, mulVec_zero]
    rw [hKdef, ← rowsMatrix_mulRows, hPK, rowsMatrix_projRows v k hk, add_mulVec, one_mulVec,
      vecMulVec_mulVec, single_dotProduct, one_mul, op_smul_eq_smul] at h1
    have h2 : ∀ a : ZMod 2, -a = a := by decide
    have h3 : y = -(y ⟨k, hk⟩ • x) := eq_neg_of_add_eq_zero_left h1
    conv_lhs => rw [h3]
    funext i
    rw [Pi.neg_apply, h2]

  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, g *ᵥ x = c • x := by
    refine ⟨(g *ᵥ x) ⟨k, hk⟩, hker _ ?_⟩
    rw [mulVec_mulVec, ← hgK, ← mulVec_mulVec, hKx, mulVec_zero]
  have hS : ∀ i < S.size, g *ᵥ toVecD d S[i]! = c • toVecD d S[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases i with _ | i
      · rw [hS0]; exact hc
      · have hi' : i < tree.length := by omega
        obtain ⟨⟨hp, hr⟩, he⟩ := hspin i hi'
        rw [he, toVecD_mulVecRows, mulVec_mulVec, hg _ hr, ← mulVec_mulVec,
          ih _ (by omega) (by omega), mulVec_smul]
  have hrows : rowsMatrix d S * gᵀ = c • rowsMatrix d S := by
    ext i j
    have := congrFun (hS i (by rw [hSd]; exact i.2)) j
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [rowsMatrix_apply]
    rw [show (S[i.val]?.getD 0) = S[i.val]! from by
      rw [getElem!_pos S i.val (by rw [hSd]; exact i.2),
        Array.getElem?_eq_getElem (by rw [hSd]; exact i.2), Option.getD_some]]
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [rowsMatrix_apply, Matrix.transpose_apply, mul_comm]
    congr 1
    rw [getElem!_pos S i.val (by rw [hSd]; exact i.2),
      Array.getElem?_eq_getElem (by rw [hSd]; exact i.2), Option.getD_some]
  have hTinv : rowsMatrix d Tinv * rowsMatrix d S = 1 := by
    rw [← rowsMatrix_mulRows, hTS, rowsMatrix_idRows]
  have hgT : gᵀ = c • 1 := by
    have := congrArg (rowsMatrix d Tinv * ·) hrows
    simp only [← mul_assoc, hTinv, one_mul, Matrix.mul_smul] at this
    exact this
  have hg1 : g = c • 1 := by
    rw [← Matrix.transpose_transpose g, hgT, Matrix.transpose_smul, Matrix.transpose_one]
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · left; rw [hg1, zero_smul]
  · right; rw [hg1, one_smul]

end CFSG.Sporadic.Schreier.PairF2
