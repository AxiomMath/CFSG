module

public import CFSG.Monster.GMS.Griess13.Checks
public import CFSG.Monster.GMS.Griess13.ChecksGlueInputs
public import Certificates.Certificate10033
public meta import CFSG.Monster.GMS.Griess13.Checks
public meta import Mathlib
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open scoped Matrix
open CFSG.Blueprint.NativeSporadic (decode)
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_mulRows rowsMatrix_idRows rowsMatrix_powRows
  rowsMatrix_apply rowsMatrix_rowsOfPayload toVecD toVecD_apply toVecD_xor toVecD_zero
  foldl_xor_toVecD ofBits_testBit)
open CFSG.Sporadic.SmallF2.Native (mulRows idRows powRows rowsOfPayload ofBits)

private theorem forall_fin_of_all {n : ℕ} {p : Fin n → Bool}
    (h : (List.finRange n).all p = true) (i : Fin n) : p i = true := by
  have := List.all_eq_true.1 h i (List.mem_finRange i)
  exact this

private theorem gCheck_true :
    gCheck = true :=
  Certificates.certificate10033.1

theorem g_pow_seven : g ^ 7 = 1 :=
  (is_prG.pow 7).eq_of PR.Is.one (by
    have := gCheck_true
    simp only [gCheck, Bool.and_eq_true] at this
    exact this.1.1)

theorem g_ne_one : g ≠ 1 :=
  is_prG.ne_of PR.Is.one (by
    have := gCheck_true
    simp only [gCheck, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1.2)

theorem g_conj_x
    (k : Fin 3) : g * xGen k * g⁻¹ = yGen k :=
  ((is_prG.mul (is_prX k)).mul is_prG.inv).eq_of (is_prY k) (by
    have := gCheck_true
    simp only [gCheck, Bool.and_eq_true] at this
    exact forall_fin_of_all this.2 k)

private theorem Tmat_eq (i : Fin 8) : Tmat i = decode 2 24 1 (tmatPay i.val) := rfl

private theorem rowsMatrix_trows (i : Fin 8) : rowsMatrix 24 (trows i.val) = Tmat i :=
  rowsMatrix_rowsOfPayload 24 (tmatPay i.val)

@[expose] def entryOf (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) (a : ℕ) : ZMod 2 :=
  if h : a < 576 then Q ⟨a / 24, by omega⟩ ⟨a % 24, by omega⟩ else 0

private theorem entryOf_add (A B : Matrix (Fin 24) (Fin 24) (ZMod 2)) (a : ℕ) :
    entryOf (A + B) a = entryOf A a + entryOf B a := by
  unfold entryOf
  split_ifs
  · rfl
  · simp

private theorem entryOf_smul (c : ZMod 2) (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) (a : ℕ) :
    entryOf (c • A) a = c * entryOf A a := by
  unfold entryOf
  split_ifs
  · rfl
  · simp

private theorem entryOf_sum {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin 24) (Fin 24) (ZMod 2))
    (a : ℕ) : entryOf (∑ i ∈ s, A i) a = ∑ i ∈ s, entryOf (A i) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold entryOf
    split_ifs <;> rfl
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, entryOf_add, ih]

private theorem freeCheck_true : freeCheck = true :=
  Certificates.certificate10033.2.1

private theorem freePos_lt :
    ∀ j : Fin 8, freePos.getD j.val 0 < 576 :=
  Certificates.certificate10033.2.2.1

theorem Tmat_free (i j : Fin 8) :
    entryOf (Tmat i) (freePos.getD j.val 0) = if i = j then 1 else 0 := by
  have h := forall_fin_of_all (forall_fin_of_all freeCheck_true i) j
  have hlt := freePos_lt j
  unfold entryOf
  simp only [hlt, ↓reduceDIte]
  rw [← rowsMatrix_trows, rowsMatrix_apply, toVecD_apply]
  simp only [beq_iff_eq] at h
  rw [h]
  by_cases hij : i = j <;> simp [hij]

private theorem oneCheck_true : oneCheck = true :=
  Certificates.certificate10033.2.2.2.1

theorem Tmat_seven : Tmat 7 = 1 := by
  have h := eqRows_iff.1 oneCheck_true
  rw [rowsMatrix_idRows] at h
  rw [← rowsMatrix_trows]
  exact h

private theorem commuteCheck_true :
    commuteCheck = true :=
  Certificates.certificate10033.2.2.2.2.1

theorem Tmat_commute
    (i : Fin 8) (k : Fin 3) :
    Tmat i * mat (xGen k) = mat (xGen k) * Tmat i := by
  have h := eqRows_iff.1 (forall_fin_of_all (forall_fin_of_all commuteCheck_true i) k)
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_trows, (is_prX k).1] at h
  exact h

theorem Tmat_independent
    (c : Fin 8 → ZMod 2) (hc : ∑ i, c i • Tmat i = 0) : c = 0 := by
  funext j
  have h := congrArg (fun Q => entryOf Q (freePos.getD j.val 0)) hc
  simp only [entryOf_sum, entryOf_smul, Tmat_free] at h
  have h0 : entryOf (0 : Matrix (Fin 24) (Fin 24) (ZMod 2)) (freePos.getD j.val 0) = 0 := by
    unfold entryOf
    split_ifs <;> rfl
  rw [h0] at h
  simpa [Finset.sum_ite_eq] using h

private def lin (b : ℕ) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) : ZMod 2 :=
  ∑ pq : Fin 24 × Fin 24, if b.testBit (24 * pq.1.val + pq.2.val) then Q pq.1 pq.2 else 0

private theorem zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

private theorem lin_xor (b b' : ℕ) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    lin (b ^^^ b') Q = lin b Q + lin b' Q := by
  unfold lin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [Nat.testBit_xor]
  cases hb : b.testBit (24 * pq.1.val + pq.2.val) <;>
    cases hb' : b'.testBit (24 * pq.1.val + pq.2.val) <;> simp [zmod2_add_self]

private theorem lin_zero (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) : lin 0 Q = 0 := by simp [lin]

private theorem lin_foldl (eqs : Array ℕ) (μ : ℕ) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (m init : ℕ) :
    lin ((List.range m).foldl (fun acc r => if μ.testBit r then acc ^^^ eqs[r]! else acc) init) Q =
      lin init Q + ∑ r ∈ Finset.range m, if μ.testBit r then lin eqs[r]! Q else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
      ← add_assoc, ← ih]
    split_ifs with h
    · rw [lin_xor]
    · rw [add_zero]

private theorem lin_eq_zero_of_subset (lam : ℕ) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (h : ∀ p q : Fin 24, lam.testBit (24 * p.val + q.val) = true → Q p q = 0) : lin lam Q = 0 := by
  unfold lin
  refine Finset.sum_eq_zero fun pq _ => ?_
  split_ifs with h1
  · exact h pq.1 pq.2 h1
  · rfl

private theorem lin_single (a : ℕ) (p q : Fin 24) (ha : a = 24 * p.val + q.val)
    (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) : lin (1 <<< a) Q = Q p q := by
  unfold lin
  rw [Finset.sum_eq_single (p, q)]
  · simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, ← ha, decide_true, ↓reduceIte]
  · intro pq _ hne
    have : ¬ (a = 24 * pq.1.val + pq.2.val) := by
      intro h
      apply hne
      have h1 : pq.1.val = p.val := by omega
      have h2 : pq.2.val = q.val := by omega
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    simp [Nat.one_shiftLeft, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem lin_ofBits (f : ℕ → Bool) (g : Fin 24 → Fin 24 → Bool)
    (hg : ∀ p q : Fin 24, f (24 * p.val + q.val) = g p q) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    lin (ofBits 576 f) Q =
      ∑ pq : Fin 24 × Fin 24, if g pq.1 pq.2 = true then Q pq.1 pq.2 else 0 := by
  unfold lin
  refine Finset.sum_congr rfl fun pq _ => ?_
  have hlt : 24 * pq.1.val + pq.2.val < 576 := by
    have := pq.1.isLt
    have := pq.2.isLt
    omega
  rw [ofBits_testBit, ← hg]
  simp [hlt]

private theorem ite_bne_add (a b : Bool) (q : ZMod 2) :
    (if (a != b) = true then q else 0) =
      (if a = true then q else 0) + (if b = true then q else 0) := by
  cases a <;> cases b <;> simp [zmod2_add_self]

private theorem eqCoeff_pair (X : Array ℕ) (i j : ℕ) (p q : Fin 24) :
    eqCoeff X i j (24 * p.val + q.val) =
      (((p.val == i) && ((X[q.val]?.getD 0).testBit j)) !=
        ((q.val == j) && ((X[i]?.getD 0).testBit p.val))) := by
  have hd : (24 * p.val + q.val) / 24 = p.val := by have := q.isLt; omega
  have hm : (24 * p.val + q.val) % 24 = q.val := by have := q.isLt; omega
  simp only [eqCoeff, hd, hm]

private def termA (X : Array ℕ) (i j : Fin 24) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (pq : Fin 24 × Fin 24) : ZMod 2 :=
  if pq.1 = i then (if (X[pq.2.val]?.getD 0).testBit j.val then Q pq.1 pq.2 else 0) else 0

private def termB (X : Array ℕ) (i j : Fin 24) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (pq : Fin 24 × Fin 24) : ZMod 2 :=
  if pq.2 = j then (if (X[i.val]?.getD 0).testBit pq.1.val then Q pq.1 pq.2 else 0) else 0

private theorem lin_eqMask {X : Array ℕ} {Xm : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (hX : rowsMatrix 24 X = Xm) (i j : Fin 24) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    lin (eqMask X i.val j.val) Q = (Q * Xm + Xm * Q) i j := by
  have hXm : ∀ l k : Fin 24, Xm l k = if (X[l.val]?.getD 0).testBit k.val then 1 else 0 := by
    intro l k
    rw [← hX, rowsMatrix_apply, toVecD_apply]
  rw [eqMask, lin_ofBits _ (fun p q => ((p.val == i.val) && ((X[q.val]?.getD 0).testBit j.val)) !=
        ((q.val == j.val) && ((X[i.val]?.getD 0).testBit p.val)))
      (fun p q => eqCoeff_pair X i.val j.val p q)]
  have h1 : ∀ pq : Fin 24 × Fin 24,
      (if (((pq.1.val == i.val) && ((X[pq.2.val]?.getD 0).testBit j.val)) !=
        ((pq.2.val == j.val) && ((X[i.val]?.getD 0).testBit pq.1.val))) = true
        then Q pq.1 pq.2 else 0) = termA X i j Q pq + termB X i j Q pq := by
    intro pq
    rw [ite_bne_add]
    congr 1
    · by_cases hp : pq.1 = i <;> simp [termA, hp, Fin.val_inj]
    · by_cases hq : pq.2 = j <;> simp [termB, hq, Fin.val_inj]
  have h2 : (∑ pq : Fin 24 × Fin 24,
      if (((pq.1.val == i.val) && ((X[pq.2.val]?.getD 0).testBit j.val)) !=
        ((pq.2.val == j.val) && ((X[i.val]?.getD 0).testBit pq.1.val))) = true
        then Q pq.1 pq.2 else 0) =
      ∑ pq : Fin 24 × Fin 24, (termA X i j Q pq + termB X i j Q pq) :=
    Finset.sum_congr rfl fun pq _ => h1 pq
  rw [h2, Finset.sum_add_distrib, Matrix.add_apply]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp only [Matrix.mul_apply, termA, ↓reduceIte]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hXm]
      split_ifs <;> simp
    · intro p _ hp
      simp [termA, hp]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Fintype.sum_prod_type_right, Finset.sum_eq_single j]
    · simp only [Matrix.mul_apply, termB, ↓reduceIte]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hXm]
      split_ifs <;> simp
    · intro q _ hq
      simp [termB, hq]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem spanCheck_true :
    spanCheckWith (eqsOf xRows) (fmaskOf freePos) certTab = true :=
  Certificates.certificate10033.2.2.2.2.2.1

private theorem lin_foldXor (eqs : Array ℕ) (μ : ℕ) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hq : ∀ r < eqs.size, lin eqs[r]! Q = 0) : lin (foldXor eqs μ) Q = 0 := by
  unfold foldXor
  rw [lin_foldl, lin_zero, zero_add]
  refine Finset.sum_eq_zero fun r hr => ?_
  split_ifs
  · exact hq r (Finset.mem_range.1 hr)
  · rfl

private theorem span_sound {eqs : Array ℕ} {fmask : ℕ} {cert : ℕ → ℕ × ℕ}
    (h : spanCheckWith eqs fmask cert = true) (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hq : ∀ r < eqs.size, lin eqs[r]! Q = 0)
    (hf : ∀ p q : Fin 24, fmask.testBit (24 * p.val + q.val) = true → Q p q = 0) :
    ∀ p q : Fin 24, Q p q = 0 := by
  intro p q
  have hlt : 24 * p.val + q.val < 576 := by
    have := p.isLt
    have := q.isLt
    omega
  by_cases hb : fmask.testBit (24 * p.val + q.val) = true
  · exact hf p q hb
  · have h1 := List.all_eq_true.1 h (24 * p.val + q.val) (List.mem_range.2 hlt)
    simp only [Bool.or_eq_true, verifyCert, Bool.and_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | ⟨h2, h3⟩
    · exact absurd h1 hb
    · have h4 : lin ((1 <<< (24 * p.val + q.val)) ^^^ (cert (24 * p.val + q.val)).2) Q = 0 := by
        rw [← h2]
        exact lin_foldXor eqs _ Q hq
      rw [lin_xor, lin_single _ p q rfl] at h4
      have h5 : lin (cert (24 * p.val + q.val)).2 Q = 0 := by
        refine lin_eq_zero_of_subset _ Q fun p' q' hlam => hf p' q' ?_
        have := congrArg (fun m => m.testBit (24 * p'.val + q'.val)) h3
        simp only [Nat.testBit_or, hlam, Bool.true_or] at this
        exact this.symm
      rw [h5, add_zero] at h4
      exact h4

private theorem eqsOf_getElem (Xs : List (Array ℕ)) (r : ℕ) (hr : r < 1728) :
    (eqsOf Xs)[r]! = eqAt Xs r := by
  unfold eqsOf
  simp [getElem!_pos, hr]

private theorem eqsOf_size (Xs : List (Array ℕ)) : (eqsOf Xs).size = 1728 := by
  simp [eqsOf]

private theorem fmaskOf_testBit {l : List ℕ} {a : ℕ} (h : (fmaskOf l).testBit a = true) :
    a ∈ l := by
  have key : ∀ (l : List ℕ) (m : ℕ),
      (l.foldl (fun m f => m ||| (1 <<< f)) m).testBit a = true → m.testBit a = true ∨ a ∈ l := by
    intro l
    induction l with
    | nil => intro m h; exact Or.inl h
    | cons f l ih =>
      intro m hm
      simp only [List.foldl_cons] at hm
      rcases ih _ hm with h1 | h1
      · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow] at h1
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons.2 (Or.inl h1.symm))
      · exact Or.inr (List.mem_cons_of_mem _ h1)
  rcases key l 0 h with h1 | h1
  · simp at h1
  · exact h1

private theorem freePos_surj :
    ∀ a ∈ freePos, ∃ j : Fin 8, freePos.getD j.val 0 = a :=
  Certificates.certificate10033.2.2.2.2.2.2.1

private theorem entryOf_pair (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) (p q : Fin 24) :
    entryOf Q (24 * p.val + q.val) = Q p q := by
  have hlt : 24 * p.val + q.val < 576 := by
    have := p.isLt
    have := q.isLt
    omega
  have hd : (24 * p.val + q.val) / 24 = p.val := by have := q.isLt; omega
  have hm : (24 * p.val + q.val) % 24 = q.val := by have := q.isLt; omega
  unfold entryOf
  simp only [hlt, ↓reduceDIte]
  congr 1 <;> exact Fin.ext (by simp [hd, hm])

private theorem xRows_getD
    (k : Fin 3) : rowsMatrix 24 (xRows.getD k.val #[]) = mat (xGen k) := by
  fin_cases k
  · exact (is_prX 0).1
  · exact (is_prX 1).1
  · exact (is_prX 2).1

private theorem lin_eqAt_zero (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hcomm : ∀ k : Fin 3, Q * mat (xGen k) = mat (xGen k) * Q) (r : ℕ) (hr : r < 1728) :
    lin (eqAt xRows r) Q = 0 := by
  have hk : r / 576 < 3 := by omega
  have hi : r % 576 / 24 < 24 := by omega
  have hj : r % 24 < 24 := by omega
  have h := lin_eqMask (xRows_getD ⟨r / 576, hk⟩) ⟨r % 576 / 24, hi⟩ ⟨r % 24, hj⟩ Q
  unfold eqAt
  rw [h, hcomm ⟨r / 576, hk⟩, Matrix.add_apply]
  exact zmod2_add_self _

private theorem commutant_vanish
    (Q : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hcomm : ∀ k : Fin 3, Q * mat (xGen k) = mat (xGen k) * Q)
    (hfree : ∀ j : Fin 8, entryOf Q (freePos.getD j.val 0) = 0) : Q = 0 := by
  have hfm : ∀ p q : Fin 24, (fmaskOf freePos).testBit (24 * p.val + q.val) = true → Q p q = 0 := by
    intro p q h
    obtain ⟨j, hj⟩ := freePos_surj _ (fmaskOf_testBit h)
    have := hfree j
    rw [hj, entryOf_pair] at this
    exact this
  have hs := spanCheck_true
  have := span_sound hs Q (fun r hr => by
    have hr' : r < 1728 := by rw [eqsOf_size] at hr; exact hr
    rw [eqsOf_getElem _ r hr']
    exact lin_eqAt_zero Q hcomm r hr') hfm
  ext p q
  exact this p q

theorem Tmat_span
    (T : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hT : ∀ k : Fin 3, T * mat (xGen k) = mat (xGen k) * T) :
    ∃ c : Fin 8 → ZMod 2, T = ∑ i, c i • Tmat i := by
  set c : Fin 8 → ZMod 2 := fun i => entryOf T (freePos.getD i.val 0) with hc
  set S : Matrix (Fin 24) (Fin 24) (ZMod 2) := ∑ i, c i • Tmat i with hS
  have hSc : ∀ k : Fin 3, S * mat (xGen k) = mat (xGen k) * S := by
    intro k
    rw [hS, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, Tmat_commute i k]
  have hQ : ∀ k : Fin 3, (T + S) * mat (xGen k) = mat (xGen k) * (T + S) := by
    intro k
    rw [add_mul, mul_add, hT k, hSc k]
  have hfree : ∀ j : Fin 8, entryOf (T + S) (freePos.getD j.val 0) = 0 := by
    intro j
    rw [entryOf_add, hS, entryOf_sum]
    simp only [entryOf_smul, Tmat_free]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hc]
    exact zmod2_add_self _
  have h0 := commutant_vanish (T + S) hQ hfree
  refine ⟨c, ?_⟩
  ext i j
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.add_apply, Matrix.zero_apply] at this
  exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ this

private theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

private theorem rowsMatrix_comboRows (c : Fin 8 → ZMod 2) :
    rowsMatrix 24 (comboRows c) = ∑ i, c i • Tmat i := by
  ext a j
  rw [rowsMatrix_apply, Matrix.sum_apply]
  unfold comboRows
  simp only [Array.getElem?_ofFn, a.isLt, ↓reduceDIte, Option.getD_some]
  rw [foldl_xor_toVecD, toVecD_zero, zero_add, Finset.sum_apply,
    ← Fin.sum_univ_eq_sum_range (fun i => (if cF c i = 1 then toVecD 24 ((trows i)[a.val]?.getD 0)
      else 0) j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : cF c i.val = c i := by simp [cF, i.isLt]
  have hT : toVecD 24 ((trows i.val)[a.val]?.getD 0) j = Tmat i a j := by
    rw [← rowsMatrix_trows, rowsMatrix_apply]
  rw [hi, Matrix.smul_apply]
  rcases zmod2_cases (c i) with h | h
  · simp [h]
  · simp [h, hT]

private theorem seventh_aux :
    ∀ c : Fin 8 → ZMod 2,
    eqRows (powRows 24 (mulRows 24 prG.r (comboRows c)) 7) (idRows 24) = true →
      eqRows (comboRows c) (idRows 24) = true :=
  Certificates.certificate10033.2.2.2.2.2.2.2.1

theorem seventh_power
    (c : Fin 8 → ZMod 2)
    (h : (mat g * ∑ i, c i • Tmat i) ^ 7 = 1) : ∑ i, c i • Tmat i = 1 := by
  have h1 : eqRows (powRows 24 (mulRows 24 prG.r (comboRows c)) 7) (idRows 24) = true := by
    rw [eqRows_iff, rowsMatrix_powRows, rowsMatrix_mulRows, rowsMatrix_comboRows,
      is_prG.1, rowsMatrix_idRows]
    exact h
  have h2 := seventh_aux c h1
  rw [eqRows_iff, rowsMatrix_comboRows, rowsMatrix_idRows] at h2
  exact h2

theorem glue_unique
    (M : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hM : ∀ k : Fin 3, M * mat (xGen k) = mat (g * xGen k * g⁻¹) * M) (h7 : M ^ 7 = 1) :
    M = mat g := by
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 24) (Fin 24) (ZMod 2), T = mat g⁻¹ * M := ⟨_, rfl⟩
  have hMT : M = mat g * T := by
    rw [hT, ← mul_assoc, mat_mul_inv, one_mul]
  have hcomm : ∀ k : Fin 3, T * mat (xGen k) = mat (xGen k) * T := by
    intro k
    have h1 : mat g⁻¹ * M * mat (xGen k) = mat g⁻¹ * (mat (g * xGen k * g⁻¹) * M) := by
      rw [mul_assoc, hM k]
    have h2 : mat g⁻¹ * (mat g * (mat (xGen k) * (mat g⁻¹ * M))) =
        mat (xGen k) * (mat g⁻¹ * M) := by
      rw [← mul_assoc (mat g⁻¹) (mat g), mat_inv_mul, one_mul]
    rw [hT, h1, mat_mul, mat_mul]
    simp only [mul_assoc]
    exact h2
  obtain ⟨c, hc⟩ := Tmat_span T hcomm
  have h7' : (mat g * ∑ i, c i • Tmat i) ^ 7 = 1 := by
    rw [← hc, ← hMT]
    exact h7
  have h1 := seventh_power c h7'
  calc M = mat g * T := hMT
    _ = mat g * ∑ i, c i • Tmat i := by rw [← hc]
    _ = mat g * 1 := by rw [h1]
    _ = mat g := mul_one _

section Generic

variable {M : Type} [Group M]

private theorem init_mem {H : Subgroup M} {inputs : List M} (h : ∀ x ∈ inputs, x ∈ H) (i : ℕ) :
    SLP.init inputs i ∈ H := by
  unfold SLP.init
  split_ifs
  · exact getD_one_mem h _
  · exact one_mem H

private theorem step_mem {H : Subgroup M} {R : ℕ → M} (hR : ∀ i, R i ∈ H)
    (l : ℕ × List (ℕ × ℤ)) (i : ℕ) : SLP.step R l i ∈ H := by
  unfold SLP.step
  by_cases hi : i = l.1
  · subst hi
    rw [Function.update_self]
    have key : ∀ (fs : List (ℕ × ℤ)) (acc : M), acc ∈ H →
        fs.foldl (fun acc f => acc * R f.1 ^ f.2) acc ∈ H := by
      intro fs
      induction fs with
      | nil => intro acc h; exact h
      | cons f fs ih =>
        intro acc h
        simp only [List.foldl_cons]
        exact ih _ (mul_mem h (zpow_mem (hR f.1) f.2))
    exact key _ _ (one_mem H)
  · rw [Function.update_of_ne hi]
    exact hR i

theorem SLP.regs_mem {H : Subgroup M} (p : SLP) {inputs : List M} (h : ∀ x ∈ inputs, x ∈ H)
    (i : ℕ) : p.regs inputs i ∈ H := by
  have key : ∀ (ls : List (ℕ × List (ℕ × ℤ))) (R : ℕ → M), (∀ i, R i ∈ H) →
      ∀ i, ls.foldl SLP.step R i ∈ H := by
    intro ls
    induction ls with
    | nil => intro R hR; exact hR
    | cons l ls ih =>
      intro R hR
      simp only [List.foldl_cons]
      exact ih _ (step_mem hR l)
  exact key p.lines _ (init_mem h) i

theorem SLP.eval_mem {H : Subgroup M} (p : SLP) {inputs : List M} (h : ∀ x ∈ inputs, x ∈ H) :
    ∀ x ∈ p.eval inputs, x ∈ H := by
  intro x hx
  unfold SLP.eval at hx
  obtain ⟨f, _, rfl⟩ := List.mem_map.1 hx
  exact zpow_mem (SLP.regs_mem p h f.1) f.2

end Generic

private theorem abCheck_true :
    abCheck = true :=
  Certificates.certificate10033.2.2.2.2.2.2.2.2

theorem genA_eq_word :
    genA = abOut.getD 0 1 :=
  is_prA.eq_of (forall₂_getD forall₂_AB_out 0) (by
    have := abCheck_true
    simp only [abCheck, Bool.and_eq_true] at this
    exact this.1)

theorem genB_eq_word :
    genB = abOut.getD 1 1 :=
  is_prB.eq_of (forall₂_getD forall₂_AB_out 1) (by
    have := abCheck_true
    simp only [abCheck, Bool.and_eq_true] at this
    exact this.2)

theorem closure_n1_n2_g :
    Subgroup.closure ({n1, n2, g} : Set G) = ⊤ := by
  have hin : ∀ x ∈ [n1, n2, g], x ∈ Subgroup.closure ({n1, n2, g} : Set G) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hout := @SLP.eval_mem G _ (Subgroup.closure ({n1, n2, g} : Set G)) (parseSLP slpWordsAB)
    [n1, n2, g] hin
  have hA : genA ∈ Subgroup.closure ({n1, n2, g} : Set G) := by
    rw [genA_eq_word]
    exact getD_one_mem hout 0
  have hB : genB ∈ Subgroup.closure ({n1, n2, g} : Set G) := by
    rw [genB_eq_word]
    exact getD_one_mem hout 1
  rw [eq_top_iff, ← closure_gen, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact hA
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hB

end CFSG.Monster.GMS.Griess13.Co1Data
