module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawInternal
public import CFSG.Mathlib.Decide.F3Rep

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Check

open CFSG.F3.Native CFSG.Decide.F3

@[expose] def mod3 (z : ℤ) : ℕ := (z % 3).toNat

@[expose] def col (t : List (List ℤ)) (N k : ℕ) : CFSG.F3.Native.V :=
  ofFnS (fun i => mod3 ((t.getD i []).getD k 0)) N

@[expose] def cols (t : List (List ℤ)) (N d : ℕ) : Array CFSG.F3.Native.V :=
  Array.ofFn (n := d) fun k => col t N k.val

@[expose] def vec (d : ℕ) (l : List ℕ) : CFSG.F3.Native.V := ofFnS (fun k => l.getD k 0) d

@[expose] def zmask (m : Fin 6) (l : List ℕ) : ℕ :=
  zeroMask (nroots m) (combS (cols (tabF m) (nroots m) (dim m)) (vec (dim m) l) (dim m))

@[expose] def zmaskH (m : Fin 6) (φ : List ℕ) : ℕ :=
  zeroMask (nroots m) (combS (cols (tabH m) (nroots m) (dim m)) (vec (dim m) φ) (dim m))

@[expose] def dotD : ℕ → List ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => dotD n a b + a.getD n 0 * b.getD n 0

@[expose] def full (m : Fin 6) : ℕ := 2 ^ nroots m - 1

@[expose] def spanOK (m : Fin 6) (l : List ℕ) (zm : ℕ) (φ : List ℕ) : Bool :=
  dotD (dim m) φ l % 3 != 0 && (zm &&& (full m ^^^ zmaskH m φ)) == 0

@[expose] def adjM (m : Fin 6) (i : ℕ) : ℕ :=
  full m ^^^ (zmask m (((tabH m).getD i []).map mod3) &&&
    zmaskH m (((tabF m).getD i []).map mod3))

@[expose] def discOK (m : Fin 6) (zm : ℕ) (T : List ℕ) : Bool :=
  T.all (· < nroots m) && !T.isEmpty && (maskOf T &&& (full m ^^^ zm)) == 0 &&
    (zm &&& (full m ^^^ maskOf T)) != 0 &&
    T.all fun i => (adjM m i &&& zm &&& (full m ^^^ maskOf T)) == 0

inductive Cert where
  | span (φ : List ℕ)
  | disc (T : List ℕ)

@[expose] def certOK (m : Fin 6) (l : List ℕ) (zm : ℕ) : Cert → Bool
  | .span φ => spanOK m l zm φ
  | .disc T => discOK m zm T

@[expose] def mulM (d : ℕ) (M : List (List ℕ)) (l : List ℕ) : List ℕ :=
  M.map fun r => dotD d r l % 3

@[expose] def dflt (m : Fin 6) (form : Option (List (List ℕ))) (l : List ℕ) (zm : ℕ) : Bool :=
  match form with
  | some M => spanOK m l zm (mulM (dim m) M l)
  | none => false

@[expose] def run (m : Fin 6) (form : Option (List (List ℕ))) :
    List (List ℕ) → List Cert → Bool
  | [], _ => true
  | l :: ls, cs =>
    if zmask m l == 0 || dflt m form l (zmask m l) then run m form ls cs
    else match cs with
      | [] => false
      | c :: cs' => certOK m l (zmask m l) c && run m form ls cs'

@[expose] def dotZ : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotZ as bs
  | _, _ => 0

@[expose] def boundOK (d : ℕ) (tF tH : List (List ℤ)) : Bool :=
  tF.all fun r => r.length == d && tH.all fun h => (dotZ r h).natAbs ≤ 2

@[expose] def pdim (m : Fin 6) : ℕ := if m.val = 3 then 6 else dim m

@[expose] def ptabF (m : Fin 6) : List (List ℤ) := if m.val = 3 then tabF 2 else tabF m

@[expose] def ptabH (m : Fin 6) : List (List ℤ) := if m.val = 3 then tabH 2 else tabH m

theorem natCast_mod3 (z : ℤ) : ((mod3 z : ℕ) : ZMod 3) = (z : ZMod 3) := by
  unfold mod3
  have hz : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
  rw [← Int.cast_natCast (R := ZMod 3) ((z % 3).toNat), Int.toNat_of_nonneg hz]
  exact ZMod.intCast_mod z 3

theorem testBit_full (m : Fin 6) (i : ℕ) : (full m).testBit i = decide (i < nroots m) := by
  unfold full
  exact Nat.testBit_two_pow_sub_one _ _

private theorem sum_fin_eq_dotZ (r h : List ℤ) :
    (∑ k : Fin r.length, r.getD k.val 0 * h.getD k.val 0) = dotZ r h := by
  induction r generalizing h with
  | nil => simp [dotZ]
  | cons a as ih =>
    cases h with
    | nil => simp [dotZ]
    | cons b bs =>
      rw [List.length_cons, Fin.sum_univ_succ]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ,
        Nat.zero_add]
      rw [ih bs]
      rfl

private theorem sum_fin_eq_dotZ_of_length {n : ℕ} (r h : List ℤ) (hlen : r.length = n) :
    (∑ k : Fin n, r.getD k.val 0 * h.getD k.val 0) = dotZ r h := by
  rw [← hlen]
  exact sum_fin_eq_dotZ r h

private theorem pairing_eq_dotZ {m : Fin 6} (i j : Root m)
    (hrlen : ((ptabF m).getD i.val []).length = pdim m) :
    pairing m i j = dotZ ((ptabF m).getD i.val []) ((ptabH m).getD j.val []) := by
  by_cases hm : m.val = 3
  · have hlen : ((tabF 2).getD i.val []).length = 6 := by
      simpa [ptabF, pdim, hm] using hrlen
    have hmain : (∑ k : Fin 6, ((tabF 2).getD i.val []).getD k 0 *
        ((tabH 2).getD j.val []).getD k 0)
        = dotZ ((tabF 2).getD i.val []) ((tabH 2).getD j.val []) :=
      sum_fin_eq_dotZ_of_length ((tabF 2).getD i.val []) ((tabH 2).getD j.val []) hlen
    simpa [pairing, ptabF, ptabH, hm] using hmain
  · have hlen : ((tabF m).getD i.val []).length = dim m := by
      simpa [ptabF, pdim, hm] using hrlen
    have hmain : (∑ k : Fin (dim m), F m i k * H m j k)
        = dotZ ((tabF m).getD i.val []) ((tabH m).getD j.val []) :=
      sum_fin_eq_dotZ_of_length ((tabF m).getD i.val []) ((tabH m).getD j.val []) hlen
    simpa [pairing, ptabF, ptabH, hm] using hmain

private theorem pairing_eq_zero_of_left_nil {m : Fin 6} {i j : Root m}
    (hi : (ptabF m).getD i.val [] = []) : pairing m i j = 0 := by
  by_cases hm : m.val = 3
  · have hi' : (tabF 2).getD i.val [] = [] := by simpa [ptabF, hm] using hi
    unfold pairing
    rw [if_pos hm, hi']
    simp
  · have hi' : (tabF m).getD i.val [] = [] := by simpa [ptabF, hm] using hi
    unfold pairing
    rw [if_neg hm]
    change (∑ k : Fin (dim m), ((tabF m).getD i []).getD k 0 *
      ((tabH m).getD j []).getD k 0) = 0
    rw [hi']
    simp

private theorem pairing_eq_zero_of_right_nil {m : Fin 6} {i j : Root m}
    (hj : (ptabH m).getD j.val [] = []) : pairing m i j = 0 := by
  by_cases hm : m.val = 3
  · have hj' : (tabH 2).getD j.val [] = [] := by simpa [ptabH, hm] using hj
    unfold pairing
    rw [if_pos hm, hj']
    simp
  · have hj' : (tabH m).getD j.val [] = [] := by simpa [ptabH, hm] using hj
    unfold pairing
    rw [if_neg hm]
    change (∑ k : Fin (dim m), ((tabF m).getD i []).getD k 0 *
      ((tabH m).getD j []).getD k 0) = 0
    rw [hj']
    simp

theorem natAbs_pairing_le {m : Fin 6} (h : boundOK (pdim m) (ptabF m) (ptabH m) = true)
    (i j : Root m) : (pairing m i j).natAbs ≤ 2 := by
  unfold boundOK at h
  have hF : ∀ r ∈ ptabF m, r.length = pdim m ∧
      ∀ h' ∈ ptabH m, (dotZ r h').natAbs ≤ 2 := by
    intro r hr
    have h1 := (List.all_eq_true.1 h) r hr
    rw [Bool.and_eq_true] at h1
    refine ⟨by simpa using h1.1, ?_⟩
    intro h' hh
    simpa using (List.all_eq_true.1 h1.2) h' hh
  by_cases hi : i.val < (ptabF m).length
  · have hr : (ptabF m).getD i.val [] ∈ ptabF m := by
      rw [List.getD_eq_getElem (l := ptabF m) (d := ([] : List ℤ)) hi]
      exact List.getElem_mem (l := ptabF m) (n := i.val) hi
    obtain ⟨hrlen, hbound⟩ := hF _ hr
    by_cases hj : j.val < (ptabH m).length
    · have hh : (ptabH m).getD j.val [] ∈ ptabH m := by
        rw [List.getD_eq_getElem (l := ptabH m) (d := ([] : List ℤ)) hj]
        exact List.getElem_mem (l := ptabH m) (n := j.val) hj
      have hb := hbound _ hh
      rw [pairing_eq_dotZ i j hrlen]
      exact hb
    · have hj0 : (ptabH m).getD j.val [] = [] :=
        List.getD_eq_default (l := ptabH m) (d := ([] : List ℤ)) (Nat.le_of_not_gt hj)
      rw [pairing_eq_zero_of_right_nil hj0]
      norm_num
  · have hi0 : (ptabF m).getD i.val [] = [] :=
      List.getD_eq_default (l := ptabF m) (d := ([] : List ℤ)) (Nat.le_of_not_gt hi)
    rw [pairing_eq_zero_of_left_nil hi0]
    norm_num

private theorem cols_getElem! (t : List (List ℤ)) (N d j : ℕ) :
    (cols t N d)[j]! = if j < d then col t N j else default := by
  unfold cols
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    simp [hj]
  · rw [getElem!_neg _ j (by simpa using hj)]
    simp [hj]

private theorem col_val (t : List (List ℤ)) (N j i : ℕ) (hi : i < N) :
    (col t N j).val i = ((mod3 ((t.getD i []).getD j 0) : ℕ) : ZMod 3) := by
  unfold col
  rw [ofFnS_eq, V.val_ofFn, if_pos hi]

private theorem vec_val (d : ℕ) (l : List ℕ) (j : ℕ) (hj : j < d) :
    (vec d l).val j = (l.getD j 0 : ZMod 3) := by
  unfold vec
  rw [ofFnS_eq, V.val_ofFn, if_pos hj]

private theorem testBit_zeroMask_combS (m : Fin 6) (t : List (List ℤ)) (l : List ℕ)
    {i : ℕ} (hi : i < nroots m) :
    (zeroMask (nroots m) (combS (cols t (nroots m) (dim m)) (vec (dim m) l) (dim m))).testBit i
        = true ↔
      (∑ j ∈ Finset.range (dim m), ((t.getD i []).getD j 0 : ZMod 3) *
        (l.getD j 0 : ZMod 3)) = 0 := by
  rw [testBit_zeroMask hi, combS_eq]
  have hY : ∀ j : ℕ, ((cols t (nroots m) (dim m))[j]!).wf = true := by
    intro j
    rw [cols_getElem!]
    by_cases hj : j < dim m
    · rw [if_pos hj]
      unfold col
      rw [ofFnS_eq]
      exact V.wf_ofFn _ _
    · rw [if_neg hj]
      exact V.wf_zero
  have hr : (vec (dim m) l).wf = true := by
    unfold vec
    rw [ofFnS_eq]
    exact V.wf_ofFn _ _
  rw [V.val_comb _ _ _ hY hr]
  have hsum : (∑ j ∈ Finset.range (dim m), (vec (dim m) l).val j *
      ((cols t (nroots m) (dim m))[j]!).val i)
      = ∑ j ∈ Finset.range (dim m), ((t.getD i []).getD j 0 : ZMod 3) *
        (l.getD j 0 : ZMod 3) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [vec_val _ _ _ (List.mem_range.1 hj), cols_getElem!, if_pos (List.mem_range.1 hj),
      col_val _ _ _ _ hi, natCast_mod3, mul_comm]
  rw [hsum]

theorem testBit_zmask {m : Fin 6} (l : List ℕ) {i : ℕ} (hi : i < nroots m) :
    (zmask m l).testBit i = true ↔ root m ⟨i, hi⟩ (vecOfList (dim m) l) = 0 := by
  unfold zmask
  rw [testBit_zeroMask_combS m (tabF m) l hi]
  have hroot : root m ⟨i, hi⟩ (vecOfList (dim m) l)
      = ∑ j ∈ Finset.range (dim m), ((tabF m).getD i []).getD j 0 *
          (l.getD j 0 : ZMod 3) := by
    rw [root_apply]
    change (∑ k : Fin (dim m), ((tabF m).getD i []).getD k.val 0 *
        (l.getD k.val 0 : ZMod 3)) = _
    rw [Fin.sum_univ_eq_sum_range (f := fun j =>
      ((tabF m).getD i []).getD j 0 * (l.getD j 0 : ZMod 3)) (n := dim m)]
  rw [hroot]

theorem testBit_zmask_of_le {m : Fin 6} (l : List ℕ) {i : ℕ} (hi : nroots m ≤ i) :
    (zmask m l).testBit i = false := by
  unfold zmask
  rw [testBit_zeroMask_of_le hi]

private theorem cast_getD_map_mod3 (t : List (List ℤ)) (i k : ℕ) :
    (((((t.getD i []).map mod3).getD k 0 : ℕ)) : ZMod 3)
      = (((t.getD i []).getD k 0 : ℤ) : ZMod 3) := by
  rw [show (0 : ℕ) = mod3 0 by decide, List.getD_map]
  exact natCast_mod3 _

theorem vecOfList_tabH {m : Fin 6} (i : Root m) :
    vecOfList (dim m) (((tabH m).getD i []).map mod3) = coroot m i := by
  funext k
  unfold vecOfList coroot H
  exact cast_getD_map_mod3 (tabH m) i k

@[expose] noncomputable def dualOf (m : Fin 6) (φ : List ℕ) : Module.Dual (ZMod 3) (V m) where
  toFun v := ∑ k : Fin (dim m), (φ.getD k.val 0 : ZMod 3) * v k
  map_add' v w := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem testBit_zmaskH {m : Fin 6} (φ : List ℕ) {i : ℕ} (hi : i < nroots m) :
    (zmaskH m φ).testBit i = true ↔ dualOf m φ (coroot m ⟨i, hi⟩) = 0 := by
  unfold zmaskH
  rw [testBit_zeroMask_combS m (tabH m) φ hi]
  have hdual : dualOf m φ (coroot m ⟨i, hi⟩)
      = ∑ j ∈ Finset.range (dim m), ((tabH m).getD i []).getD j 0 *
          (φ.getD j 0 : ZMod 3) := by
    change (∑ k : Fin (dim m), (φ.getD k.val 0 : ZMod 3) *
        ((tabH m).getD i []).getD k.val 0) = _
    rw [Fin.sum_univ_eq_sum_range (f := fun j =>
      (φ.getD j 0 : ZMod 3) * ((tabH m).getD i []).getD j 0) (n := dim m)]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  rw [hdual]

private theorem sum_range_mul_eq_dotD (n : ℕ) (φ l : List ℕ) :
    (∑ k ∈ Finset.range n, (φ.getD k 0 : ZMod 3) * (l.getD k 0 : ZMod 3))
      = (dotD n φ l : ZMod 3) := by
  induction n with
  | zero => simp [dotD]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show dotD (n + 1) φ l = dotD n φ l + φ.getD n 0 * l.getD n 0 from rfl]
    push_cast
    rfl

theorem dualOf_vecOfList (m : Fin 6) (φ l : List ℕ) :
    dualOf m φ (vecOfList (dim m) l) = (dotD (dim m) φ l : ZMod 3) := by
  change (∑ k : Fin (dim m), (φ.getD k.val 0 : ZMod 3) * (l.getD k.val 0 : ZMod 3))
      = (dotD (dim m) φ l : ZMod 3)
  rw [Fin.sum_univ_eq_sum_range (f := fun j =>
    (φ.getD j 0 : ZMod 3) * (l.getD j 0 : ZMod 3)) (n := dim m)]
  exact sum_range_mul_eq_dotD (dim m) φ l

theorem dualOf_tabF {m : Fin 6} (i : Root m) :
    dualOf m (((tabF m).getD i []).map mod3) = root m i := by
  apply LinearMap.ext
  intro v
  rw [root_apply]
  change (∑ k : Fin (dim m), (((((tabF m).getD i []).map mod3).getD k.val 0 : ℕ) : ZMod 3) *
      v k) = ∑ k : Fin (dim m), (F m i k : ZMod 3) * v k
  apply Finset.sum_congr rfl
  intro k _
  rw [cast_getD_map_mod3]
  rfl

end CFSG.StandardType.GGQ2Frame.ExcRaw.Check
