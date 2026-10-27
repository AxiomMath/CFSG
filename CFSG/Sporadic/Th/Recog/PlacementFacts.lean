module

public import CFSG.Sporadic.Th.Recog.JLetters
public import Certificates.Certificate687006
public import CFSG.Certificates.WordPresentation

public section

namespace CFSG.Sporadic.Th.Recog.Place

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords

theorem get1_ofFn {n : ℕ} (f : Fin n → Array V4) (i : Fin n) : get1 (Array.ofFn f) i = f i := by
  simp [get1, Array.getElem?_ofFn, i.isLt]

theorem get2_ofFn {n k : ℕ} (f : Fin n → Fin k → Array V4) (i : Fin n) (m : Fin k) :
    get2 (Array.ofFn fun i => Array.ofFn (f i)) i m = f i m := by
  simp [get2, Array.getElem?_ofFn, i.isLt, m.isLt]

section Elements


theorem lJ_eq (i : Fin 6) : lJ i = wprod hswJ (lWord i) := by
  apply toMat_injective
  rw [← rowsMatrix_rowsL i]
  exact rowsMatrix_wRowsArr _ _ hswJ (fun j => by rw [rowsHswArr_get]; exact rowsMatrix_rowsHsw j)
    (fun j => by rw [rowsHswInvArr_get]; exact rowsMatrix_rowsHswInv j) (lWord i)

@[expose] noncomputable def v (i : Fin 2) : J := wprod hswJ (vWord i)

@[expose] noncomputable def hgen (j : Fin 5) : J := wprod lJ (hWord j)

@[expose] noncomputable def wp (i : Fin 2) : J := wprod lJ (wpWord i)

@[expose] noncomputable def orb (i : Fin 2) (r : Fin 18) : J := wprod hgen (orbWord i r)

@[expose] noncomputable def rep (i : Fin 2) (m : Fin 8) : J := wprod hgen (repWord i m)

@[expose] noncomputable def four (i : Fin 2) : Fin 4 → J := ![1, hswJ 0, v i, hswJ 0 * v i]

@[expose] noncomputable def cent (i : Fin 2) (q : Fin 32) : J :=
  rep i (split32 q).1 * four i (split32 q).2

@[expose] noncomputable def z (i : Fin 2) (m : Fin 8) : J := wp i * rep i m

@[expose] noncomputable def gens (x : Fin 2) : Fin 4 → J :=
  ![v 0, v 1, z 0 (pair x).1, z 1 (pair x).2]

structure Base.Spec (B : Base) : Prop where
  H : ∀ i : Fin 8, rowsMatrix (get1 B.H i) = toMat (hswJ i)
  HI : ∀ i : Fin 8, rowsMatrix (get1 B.HI i) = toMat (hswJ i)⁻¹
  L : ∀ i : Fin 6, rowsMatrix (get1 B.L i) = toMat (lJ i)
  LI : ∀ i : Fin 6, rowsMatrix (get1 B.LI i) = toMat (lJ i)⁻¹
  h : ∀ j : Fin 5, rowsMatrix (get1 B.h j) = toMat (hgen j)
  hI : ∀ j : Fin 5, rowsMatrix (get1 B.hI j) = toMat (hgen j)⁻¹
  W : ∀ i : Fin 2, rowsMatrix (get1 B.W i) = toMat (wp i)
  WI : ∀ i : Fin 2, rowsMatrix (get1 B.WI i) = toMat (wp i)⁻¹
  V : ∀ i : Fin 2, rowsMatrix (get1 B.V i) = toMat (v i)
  VI : ∀ i : Fin 2, rowsMatrix (get1 B.VI i) = toMat (v i)⁻¹
  R : ∀ (i : Fin 2) (m : Fin 8), rowsMatrix (get2 B.R i m) = toMat (rep i m)
  Z : ∀ (i : Fin 2) (m : Fin 8), rowsMatrix (get2 B.Z i m) = toMat (z i m)
  A : rowsMatrix B.A = toMat (hswJ 0)
  D : rowsMatrix B.D = toMat (hswJ 3)
  DI : rowsMatrix B.DI = toMat (hswJ 3)⁻¹

theorem Base.make_spec' {H HI : Array (Array V4)}
    (hH : ∀ i : Fin 8, rowsMatrix (get1 H i) = toMat (hswJ i))
    (hHI : ∀ i : Fin 8, rowsMatrix (get1 HI i) = toMat (hswJ i)⁻¹) : (Base.make H HI).Spec := by
  have hL : ∀ i : Fin 6, rowsMatrix (get1 (Array.ofFn fun i => wRowsArr H HI (lWord i)) i) =
      toMat (lJ i) := fun i => by
    rw [get1_ofFn, lJ_eq]; exact rowsMatrix_wRowsArr H HI hswJ hH hHI (lWord i)
  have hLI : ∀ i : Fin 6, rowsMatrix (get1 (Array.ofFn fun i =>
      wRowsArr H HI (FreeGroup.invRev (lWord i))) i) = toMat (lJ i)⁻¹ := fun i => by
    rw [get1_ofFn, rowsMatrix_wRowsArr H HI hswJ hH hHI, wprod_invRev, lJ_eq]
  have hh : ∀ j : Fin 5, rowsMatrix (get1 (Array.ofFn fun j => wRowsArr
      (Array.ofFn fun i => wRowsArr H HI (lWord i))
      (Array.ofFn fun i => wRowsArr H HI (FreeGroup.invRev (lWord i))) (hWord j)) j) =
      toMat (hgen j) := fun j => by
    rw [get1_ofFn]; exact rowsMatrix_wRowsArr _ _ lJ hL hLI (hWord j)
  have hhI : ∀ j : Fin 5, rowsMatrix (get1 (Array.ofFn fun j => wRowsArr
      (Array.ofFn fun i => wRowsArr H HI (lWord i))
      (Array.ofFn fun i => wRowsArr H HI (FreeGroup.invRev (lWord i)))
      (FreeGroup.invRev (hWord j))) j) = toMat (hgen j)⁻¹ := fun j => by
    rw [get1_ofFn, rowsMatrix_wRowsArr _ _ lJ hL hLI, wprod_invRev]; rfl
  have hW : ∀ i : Fin 2, rowsMatrix (get1 (Array.ofFn fun i => wRowsArr
      (Array.ofFn fun i => wRowsArr H HI (lWord i))
      (Array.ofFn fun i => wRowsArr H HI (FreeGroup.invRev (lWord i))) (wpWord i)) i) =
      toMat (wp i) := fun i => by
    rw [get1_ofFn]; exact rowsMatrix_wRowsArr _ _ lJ hL hLI (wpWord i)
  have hR : ∀ (i : Fin 2) (m : Fin 8), rowsMatrix (get2 (Array.ofFn fun i => Array.ofFn fun m =>
      wRowsArr (Array.ofFn fun j => wRowsArr
        (Array.ofFn fun i => wRowsArr H HI (lWord i))
        (Array.ofFn fun i => wRowsArr H HI (FreeGroup.invRev (lWord i))) (hWord j))
      (Array.ofFn fun j => wRowsArr
        (Array.ofFn fun i => wRowsArr H HI (lWord i))
        (Array.ofFn fun i => wRowsArr H HI (FreeGroup.invRev (lWord i)))
        (FreeGroup.invRev (hWord j))) (repWord i m)) i m) = toMat (rep i m) := fun i m => by
    rw [get2_ofFn]; exact rowsMatrix_wRowsArr _ _ hgen hh hhI (repWord i m)
  refine ⟨hH, hHI, hL, hLI, hh, hhI, hW, fun i => ?_, fun i => ?_, fun i => ?_, hR,
    fun i m => ?_, hH 0, hH 3, hHI 3⟩
  · show rowsMatrix (get1 (Array.ofFn fun i => wRowsArr _ _ (FreeGroup.invRev (wpWord i))) i) = _
    rw [get1_ofFn, rowsMatrix_wRowsArr _ _ lJ hL hLI, wprod_invRev]; rfl
  · show rowsMatrix (get1 (Array.ofFn fun i => wRowsArr H HI (vWord i)) i) = _
    rw [get1_ofFn]; exact rowsMatrix_wRowsArr H HI hswJ hH hHI (vWord i)
  · show rowsMatrix (get1 (Array.ofFn fun i => wRowsArr H HI (FreeGroup.invRev (vWord i))) i) = _
    rw [get1_ofFn, rowsMatrix_wRowsArr H HI hswJ hH hHI, wprod_invRev]; rfl
  · show rowsMatrix (get2 (Array.ofFn fun i => Array.ofFn fun m => mulRows (get1 _ i)
      (get2 _ i m)) i m) = _
    rw [get2_ofFn, rowsMatrix_mulRows, hW i, hR i m, ← toMat_mul]; rfl

theorem Base.make_spec : (Base.make (rowsHswArr ()) (rowsHswInvArr ())).Spec :=
  Base.make_spec' (fun i => by rw [get1, rowsHswArr_get]; exact rowsMatrix_rowsHsw i)
    (fun i => by rw [get1, rowsHswInvArr_get]; exact rowsMatrix_rowsHswInv i)

end Elements


section Sound


private theorem rows_mul {X Y : Array V4} {g h : J} (hX : rowsMatrix X = toMat g)
    (hY : rowsMatrix Y = toMat h) : rowsMatrix (mulRows X Y) = toMat (g * h) := by
  rw [rowsMatrix_mulRows, hX, hY, toMat_mul]

private theorem rows_one : rowsMatrix idRows = toMat (1 : J) := by
  rw [rowsMatrix_idRows, toMat_one]

private theorem rows_word {n : ℕ} {rs rsi : Array (Array V4)} {g : Fin n → J}
    (h : ∀ i : Fin n, rowsMatrix (get1 rs i) = toMat (g i))
    (hi : ∀ i : Fin n, rowsMatrix (get1 rsi i) = toMat (g i)⁻¹) (w : List (Fin n × Bool)) :
    rowsMatrix (wRowsArr rs rsi w) = toMat (wprod g w) :=
  rowsMatrix_wRowsArr rs rsi g h hi w

private theorem rows_wordInv {n : ℕ} {rs rsi : Array (Array V4)} {g : Fin n → J}
    (h : ∀ i : Fin n, rowsMatrix (get1 rs i) = toMat (g i))
    (hi : ∀ i : Fin n, rowsMatrix (get1 rsi i) = toMat (g i)⁻¹) (w : List (Fin n × Bool)) :
    rowsMatrix (wRowsArr rs rsi (FreeGroup.invRev w)) = toMat (wprod g w)⁻¹ := by
  rw [rows_word h hi, wprod_invRev]

private theorem eq_of_rows {X Y : Array V4} {g h : J} (hX : rowsMatrix X = toMat g)
    (hY : rowsMatrix Y = toMat h) (e : eqRows X Y = true) : g = h :=
  toMat_injective (hX.symm.trans ((rowsMatrix_eq_of_eqRows e).trans hY))

private theorem isRows_canon {X : Array V4} {g : J} (hX : rowsMatrix X = toMat g) :
    IsRows (canon X) g :=
  ⟨transposeRows_size _, transposeRows_wf _, by
    rw [canon, rowsMatrix_transposeRows, rowsMatrix_transposeRows, Matrix.transpose_transpose, hX]⟩

private theorem ne_one_of_rows {X : Array V4} {g : J} (hX : rowsMatrix X = toMat g)
    (e : eqRows (canon X) idRows = false) : g ≠ 1 :=
  (isRows_canon hX).ne_of_eqRows IsRows.one e

private theorem nodup_of_rows {n : ℕ} {X : Fin n → Array V4} {g : Fin n → J}
    (hX : ∀ r, rowsMatrix (X r) = toMat (g r)) (e : (List.ofFn fun r => canon (X r)).Nodup) :
    (List.ofFn g).Nodup := by
  rw [List.nodup_ofFn] at e ⊢
  intro r s hrs
  exact e ((isRows_canon (hX r)).rows_eq (hrs ▸ isRows_canon (hX s)))

private theorem orderOf_of_ord8 {X : Array V4} {g : J} (hX : rowsMatrix X = toMat g)
    (e : ord8 X = true) : orderOf g = 8 := by
  simp only [ord8, Bool.and_eq_true, Bool.not_eq_true'] at e
  have r2 : rowsMatrix (mulRows X X) = toMat (g ^ 2) := by rw [rows_mul hX hX, sq]
  have r4 : rowsMatrix (mulRows (mulRows X X) (mulRows X X)) = toMat (g ^ 4) := by
    rw [rows_mul r2 r2, ← pow_add]
  have h8 : g ^ 2 ^ (2 + 1) = 1 := by
    have h := eq_of_rows (rows_mul r4 r4) rows_one e.1
    rwa [← pow_add] at h
  have h4 : ¬ g ^ 2 ^ 2 = 1 := ne_one_of_rows r4 e.2
  exact orderOf_eq_prime_pow h4 h8

private theorem rows_four {B : Base} (hB : B.Spec) (i : Fin 2) (u : Fin 4) :
    rowsMatrix (fourRows B i u) = toMat (four i u) := by
  fin_cases u
  · exact rows_one
  · exact hB.A
  · exact hB.V i
  · exact rows_mul hB.A (hB.V i)

theorem checkA_sound {B : Base} (hB : B.Spec) (e : checkA B = true) :
    wprod hgen aHWord = hswJ 0 ∧ hswJ 0 * hswJ 0 = 1 := by
  simp only [checkA, Bool.and_eq_true] at e
  exact ⟨eq_of_rows (rows_word hB.h hB.hI aHWord) hB.A e.1,
    eq_of_rows (rows_mul hB.A hB.A) rows_one e.2⟩

theorem checkV_sound {B : Base} (hB : B.Spec) (e : checkV B = true) :
    (∀ i, v i * v i = 1 ∧ hswJ 0 * v i = v i * hswJ 0) ∧ v 0 * v 1 * (v 0 * v 1) = hswJ 0 := by
  simp only [checkV, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at e
  refine ⟨fun i => ⟨eq_of_rows (rows_mul (hB.V i) (hB.V i)) rows_one (e.1 i).1,
    eq_of_rows (rows_mul hB.A (hB.V i)) (rows_mul (hB.V i) hB.A) (e.1 i).2⟩, ?_⟩
  exact eq_of_rows (rows_mul (rows_mul (hB.V 0) (hB.V 1)) (rows_mul (hB.V 0) (hB.V 1))) hB.A e.2

theorem checkH_sound {B : Base} (hB : B.Spec) (e : checkH B = true) (j : Fin 5) :
    hgen j * hswJ 0 = hswJ 0 * hgen j := by
  simp only [checkH, List.all_eq_true, List.mem_finRange, true_implies] at e
  exact eq_of_rows (rows_mul (hB.h j) hB.A) (rows_mul hB.A (hB.h j)) (e j)

theorem checkOrb_sound {B : Base} (hB : B.Spec) (e : checkOrb B = true) (i : Fin 2) :
    (List.ofFn fun r => orb i r * v i * (orb i r)⁻¹).Nodup := by
  simp only [checkOrb, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at e
  exact nodup_of_rows (fun r => rows_mul (rows_mul (rows_word hB.h hB.hI (orbWord i r)) (hB.V i))
    (rows_wordInv hB.h hB.hI (orbWord i r))) (e i)

theorem checkRep_sound {B : Base} (hB : B.Spec) (e : checkRep B = true) (i : Fin 2) (m : Fin 8) :
    rep i m * v i = v i * rep i m := by
  simp only [checkRep, List.all_eq_true, List.mem_finRange, true_implies] at e
  exact eq_of_rows (rows_mul (hB.R i m) (hB.V i)) (rows_mul (hB.V i) (hB.R i m)) (e i m)

theorem checkCent_sound {B : Base} (hB : B.Spec) (e : checkCent B = true) (i : Fin 2) :
    (List.ofFn (cent i)).Nodup := by
  simp only [checkCent, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at e
  exact nodup_of_rows (fun q => rows_mul (hB.R i _) (rows_four hB i _)) (e i)

theorem checkWp_sound {B : Base} (hB : B.Spec) (e : checkWp B = true) (i : Fin 2) :
    wp i * hswJ 0 * (wp i)⁻¹ = v i ∧ wp i * v i * (wp i)⁻¹ = hswJ 0 * v i := by
  simp only [checkWp, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at e
  exact ⟨eq_of_rows (rows_mul (rows_mul (hB.W i) hB.A) (hB.WI i)) (hB.V i) (e i).1,
    eq_of_rows (rows_mul (rows_mul (hB.W i) (hB.V i)) (hB.WI i)) (rows_mul hB.A (hB.V i)) (e i).2⟩

theorem checkCoset_sound {B : Base} (hB : B.Spec) (e : checkCoset B = true) (i : Fin 2)
    (m : Fin 8) :
    m ∈ good i ∨ (∀ u, (z i m * four i u) ^ 3 ≠ 1) ∨ orderOf (v (1 - i) * z i m) = 8 := by
  simp only [checkCoset, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    List.contains_iff_mem] at e
  rcases e i m with (h | h) | h
  · exact Or.inl h
  · refine Or.inr (Or.inl fun u h3 => ?_)
    have hc := h u
    simp only [cubeNe, Bool.not_eq_true'] at hc
    have r := rows_mul (hB.Z i m) (rows_four hB i u)
    exact ne_one_of_rows (rows_mul (rows_mul r r) r) hc (by rw [← pow_three']; exact h3)
  · exact Or.inr (Or.inr (orderOf_of_ord8 (rows_mul (hB.V (1 - i)) (hB.Z i m)) h))

theorem checkPair_sound {B : Base} (hB : B.Spec) (e : checkPair B = true) {m₀ m₁ : Fin 8}
    (h₀ : m₀ ∈ good 0) (h₁ : m₁ ∈ good 1) :
    (∃ x, pair x = (m₀, m₁)) ∨ orderOf (z 0 m₀ * (hswJ 3 * (v 0 * z 1 m₁) * (hswJ 3)⁻¹)) = 8 := by
  simp only [checkPair, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at e
  rcases e m₀ h₀ m₁ h₁ with (h | h) | h
  · exact Or.inl ⟨0, h⟩
  · exact Or.inl ⟨1, h⟩
  · exact Or.inr (orderOf_of_ord8 (rows_mul (hB.Z 0 m₀)
      (rows_mul (rows_mul hB.D (rows_mul (hB.V 0) (hB.Z 1 m₁))) hB.DI)) h)

private theorem rows_gens {B : Base} (hB : B.Spec) (x : Fin 2) (q : Fin 4) :
    rowsMatrix (get1 (gensRows B x) q) = toMat (gens x q) := by
  fin_cases q
  · exact hB.V 0
  · exact hB.V 1
  · exact hB.Z 0 _
  · exact hB.Z 1 _

private theorem rows_zInv {B : Base} (hB : B.Spec) (i : Fin 2) (m : Fin 8) :
    rowsMatrix (zInvRows B i m) = toMat (z i m)⁻¹ := by
  rw [zInvRows, rows_mul (rows_wordInv hB.h hB.hI (repWord i m)) (hB.WI i), z, mul_inv_rev]
  rfl

private theorem rows_gensInv {B : Base} (hB : B.Spec) (x : Fin 2) (q : Fin 4) :
    rowsMatrix (get1 (gensInvRows B x) q) = toMat (gens x q)⁻¹ := by
  fin_cases q
  · exact hB.VI 0
  · exact hB.VI 1
  · exact rows_zInv hB 0 _
  · exact rows_zInv hB 1 _

theorem checkXw_sound {B : Base} (hB : B.Spec) (e : checkXw B = true) (x : Fin 2) (k : Twist)
    (j : Fin 2) : wprod hswJ (xw (k, x) j) = wprod (gens x) (xwExpr k x j) := by
  simp only [checkXw, List.all_eq_true, List.mem_finRange, true_implies] at e
  have hk : k ∈ [Twist.id, .f1, .f3, .f13] := by cases k <;> simp
  exact eq_of_rows (rows_word hB.H hB.HI _) (rows_word (rows_gens hB x) (rows_gensInv hB x) _)
    (e x k hk j)

end Sound

section Facts


private theorem check_spec :
    checkA (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkV (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkH (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkOrb (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkRep (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkCent (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkWp (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkCoset (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkPair (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true ∧
    checkXw (Base.make (rowsHswArr ()) (rowsHswInvArr ())) = true := by
  have h := Certificates.certificate687006
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem wprod_hgen_aHWord : wprod hgen aHWord = hswJ 0 :=
  (checkA_sound Base.make_spec check_spec.1).1

theorem hswJ_zero_mul_self : hswJ 0 * hswJ 0 = 1 :=
  (checkA_sound Base.make_spec check_spec.1).2

theorem v_mul_self (i : Fin 2) : v i * v i = 1 :=
  ((checkV_sound Base.make_spec check_spec.2.1).1 i).1

theorem hswJ_zero_comm_v (i : Fin 2) : hswJ 0 * v i = v i * hswJ 0 :=
  ((checkV_sound Base.make_spec check_spec.2.1).1 i).2

theorem v_mul_v_mul_self : v 0 * v 1 * (v 0 * v 1) = hswJ 0 :=
  (checkV_sound Base.make_spec check_spec.2.1).2

theorem hgen_comm (j : Fin 5) : hgen j * hswJ 0 = hswJ 0 * hgen j :=
  checkH_sound Base.make_spec check_spec.2.2.1 j

theorem orb_nodup (i : Fin 2) : (List.ofFn fun r => orb i r * v i * (orb i r)⁻¹).Nodup :=
  checkOrb_sound Base.make_spec check_spec.2.2.2.1 i

theorem rep_comm (i : Fin 2) (m : Fin 8) : rep i m * v i = v i * rep i m :=
  checkRep_sound Base.make_spec check_spec.2.2.2.2.1 i m

theorem cent_nodup (i : Fin 2) : (List.ofFn (cent i)).Nodup :=
  checkCent_sound Base.make_spec check_spec.2.2.2.2.2.1 i

theorem wp_conj_a (i : Fin 2) : wp i * hswJ 0 * (wp i)⁻¹ = v i :=
  (checkWp_sound Base.make_spec check_spec.2.2.2.2.2.2.1 i).1

theorem wp_conj_v (i : Fin 2) : wp i * v i * (wp i)⁻¹ = hswJ 0 * v i :=
  (checkWp_sound Base.make_spec check_spec.2.2.2.2.2.2.1 i).2

theorem coset_cases (i : Fin 2) (m : Fin 8) :
    m ∈ good i ∨ (∀ u, (z i m * four i u) ^ 3 ≠ 1) ∨ orderOf (v (1 - i) * z i m) = 8 :=
  checkCoset_sound Base.make_spec check_spec.2.2.2.2.2.2.2.1 i m

theorem pair_cases {m₀ m₁ : Fin 8} (h₀ : m₀ ∈ good 0) (h₁ : m₁ ∈ good 1) :
    (∃ x, pair x = (m₀, m₁)) ∨ orderOf (z 0 m₀ * (hswJ 3 * (v 0 * z 1 m₁) * (hswJ 3)⁻¹)) = 8 :=
  checkPair_sound Base.make_spec check_spec.2.2.2.2.2.2.2.2.1 h₀ h₁

theorem xw_eq (x : Fin 2) (k : Twist) (j : Fin 2) :
    wprod hswJ (xw (k, x) j) = wprod (gens x) (xwExpr k x j) :=
  checkXw_sound Base.make_spec check_spec.2.2.2.2.2.2.2.2.2 x k j

theorem v_zero : v 0 = hswJ 3 * hswJ 2 * hswJ 3 := by
  simp [v, vWord, wprod, mul_assoc]

theorem v_one : v 1 = hswJ 2 := by
  simp [v, vWord, wprod]

theorem hgen_mem_K₀ (j : Fin 5) : hgen j ∈ Subgroup.closure (Set.range lJ) :=
  CFSG.Certificates.signedProd_mem (fun i => Subgroup.subset_closure (Set.mem_range_self i)) _

theorem wp_mem_K₀ (i : Fin 2) : wp i ∈ Subgroup.closure (Set.range lJ) :=
  CFSG.Certificates.signedProd_mem (fun i => Subgroup.subset_closure (Set.mem_range_self i)) _

theorem hswJ_zero_mem_K₀ : hswJ 0 ∈ Subgroup.closure (Set.range lJ) :=
  wprod_hgen_aHWord ▸ CFSG.Certificates.signedProd_mem hgen_mem_K₀ aHWord

private theorem cent_small (i : Fin 2) :
    cent i 0 = 1 ∧ cent i 1 = hswJ 0 ∧ cent i 2 = v i := by
  have hr : rep i 0 = 1 := by fin_cases i <;> rfl
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cent, show split32 0 = (0, 0) from rfl, show split32 1 = (0, 1) from rfl,
      show split32 2 = (0, 2) from rfl, hr, one_mul] <;> rfl

theorem hswJ_zero_ne_one : hswJ 0 ≠ 1 := by
  have h := (List.nodup_ofFn.mp (cent_nodup 0)).ne (show (1 : Fin 32) ≠ 0 by decide)
  rwa [(cent_small 0).2.1, (cent_small 0).1] at h

theorem v_ne_one (i : Fin 2) : v i ≠ 1 := by
  have h := (List.nodup_ofFn.mp (cent_nodup i)).ne (show (2 : Fin 32) ≠ 0 by decide)
  rwa [(cent_small i).2.2, (cent_small i).1] at h

theorem hswJ_zero_ne_v (i : Fin 2) : hswJ 0 ≠ v i := by
  have h := (List.nodup_ofFn.mp (cent_nodup i)).ne (show (1 : Fin 32) ≠ 2 by decide)
  rwa [(cent_small i).2.1, (cent_small i).2.2] at h

end Facts

end CFSG.Sporadic.Th.Recog.Place
