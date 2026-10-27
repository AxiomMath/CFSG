module

public import CFSG.LocalAnalysis.StandardType.GGResICell

public section

namespace CFSG.StandardType.GGCellN

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def bor (a b : Bool) : Bool := Bool.rec b true a

@[expose] noncomputable def bnot (a : Bool) : Bool := Bool.rec true false a

theorem band_eq (a b : Bool) : band a b = (a && b) := by cases a <;> rfl

theorem bor_eq (a b : Bool) : bor a b = (a || b) := by cases a <;> rfl

theorem bnot_eq (a : Bool) : bnot a = !a := by cases a <;> rfl

@[expose] noncomputable def nthD {α : Type} (d : α) (l : List α) : ℕ → α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun a _ ih i => Nat.rec (motive := fun _ => α) a (fun j _ => ih j) i) l

@[expose] noncomputable def nth (l : List ℕ) (i : ℕ) : ℕ := nthD 0 l i

@[expose] noncomputable def nthL (l : List (List ℕ)) (i : ℕ) : List ℕ := nthD [] l i

@[expose] noncomputable def ofA {α : Type} (f : ℕ → α) (m : ℕ) : ℕ → List α :=
  Nat.rec (motive := fun _ => ℕ → List α) (fun _ => []) (fun _ ih s => f s :: ih (Nat.succ s)) m

theorem nthD_ofA {α : Type} (d : α) (f : ℕ → α) (m s i : ℕ) (h : i < m) :
    nthD d (ofA f m s) i = f (s + i) := by
  induction m generalizing s i with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have h' := ih (s + 1) j (by omega)
      rw [show s + (j + 1) = s + 1 + j by omega, ← h']
      rfl

@[expose] noncomputable def allR (p : ℕ → Bool) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => band acc (p k)) m

@[expose] noncomputable def anyR (p : ℕ → Bool) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => bor acc (p k)) m

theorem allR_iff (p : ℕ → Bool) (m : ℕ) : allR p m = true ↔ ∀ i < m, p i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    change band (allR p m) (p m) = true ↔ _
    rw [band_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hi' : i < m
      · exact h1 i hi'
      · obtain rfl : i = m := by omega
        exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

theorem anyR_iff (p : ℕ → Bool) (m : ℕ) : anyR p m = true ↔ ∃ i < m, p i = true := by
  induction m with
  | zero =>
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    change bor (anyR p m) (p m) = true ↔ _
    rw [bor_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hi' : i < m
      · exact Or.inl ⟨i, hi', h⟩
      · obtain rfl : i = m := by omega
        exact Or.inr h

theorem allR_eq_finRange (p : ℕ → Bool) (m : ℕ) :
    allR p m = (List.finRange m).all (fun i => p i.val) := by
  rw [Bool.eq_iff_iff, allR_iff, List.all_eq_true]
  exact ⟨fun h i _ => h i i.isLt, fun h i hi => h ⟨i, hi⟩ (List.mem_finRange _)⟩

theorem any_range (p : ℕ → Bool) (m : ℕ) : (List.range m).any p = anyR p m := by
  rw [Bool.eq_iff_iff, anyR_iff, List.any_eq_true]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, List.mem_range.1 hi, h⟩,
    fun ⟨i, hi, h⟩ => ⟨i, List.mem_range.2 hi, h⟩⟩

theorem all_finRange {m : ℕ} (p : Fin m → Bool) (p' : ℕ → Bool) (h : ∀ i : Fin m, p i = p' i.val) :
    (List.finRange m).all p = allR p' m := by
  rw [allR_eq_finRange]
  exact congrArg (List.all _) (funext h)

@[expose] noncomputable def allL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => band (p a) ih) l

@[expose] noncomputable def pwN {α : Type} (r : α → α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih => band (allL (r a) t) ih) l

theorem allL_eq {α : Type} (p : α → Bool) (l : List α) : allL p l = l.all p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change band (p a) (allL p t) = _
    rw [band_eq, ih, List.all_cons]

theorem pwN_nodup {α β : Type} [DecidableEq β] (f : α → β) (r : α → α → Bool)
    (hr : ∀ a b, r a b = !decide (f a = f b)) (l : List α) :
    pwN r l = decide (l.map f).Nodup := by
  induction l with
  | nil => exact (decide_eq_true List.nodup_nil).symm
  | cons a t ih =>
    change band (allL (r a) t) (pwN r t) = _
    rw [band_eq, ih, allL_eq, Bool.eq_iff_iff, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_iff, decide_eq_true_iff, List.map_cons, List.nodup_cons, List.mem_map]
    simp only [hr, Bool.not_eq_true', decide_eq_false_iff_not, not_exists, not_and]
    exact and_congr_left' (forall₂_congr fun x _ => not_congr eq_comm)

section Res

variable (q : ℕ)

@[expose] noncomputable def addq (a b : ℕ) : ℕ := Nat.mod (Nat.add a b) q

@[expose] noncomputable def mulq (a b : ℕ) : ℕ := Nat.mod (Nat.mul a b) q

@[expose] noncomputable def subq (a b : ℕ) : ℕ := Nat.mod (Nat.add a (Nat.mul (Nat.sub q 1) b)) q

@[expose] noncomputable def eqq (a b : ℕ) : Bool := Nat.beq (Nat.mod a q) (Nat.mod b q)

@[expose] noncomputable def zq (x : ℤ) : ℕ := Int.toNat (Int.emod x (q : ℤ))

@[expose] noncomputable def tq (τ' : ℕ) : ℕ := Nat.mod (Nat.add τ' (Nat.mul 8 (Nat.sub q 1))) q

@[expose] noncomputable def sumR (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => addq q acc (f k)) m

variable {q} [NeZero q]

theorem cast_addq (a b : ℕ) : ((addq q a b : ℕ) : ZMod q) = a + b := by
  change (((a + b) % q : ℕ) : ZMod q) = _
  rw [ZMod.natCast_mod, Nat.cast_add]

theorem cast_mulq (a b : ℕ) : ((mulq q a b : ℕ) : ZMod q) = a * b := by
  change (((a * b) % q : ℕ) : ZMod q) = _
  rw [ZMod.natCast_mod, Nat.cast_mul]

theorem cast_qm1 : ((q - 1 : ℕ) : ZMod q) = -1 := by
  rw [Nat.cast_sub (NeZero.one_le), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem cast_subq (a b : ℕ) : ((subq q a b : ℕ) : ZMod q) = a - b := by
  change (((a + (q - 1) * b) % q : ℕ) : ZMod q) = _
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, cast_qm1]
  ring

theorem cast_tq (τ' : ℕ) : ((tq q τ' : ℕ) : ZMod q) = (((τ' : ℤ) - 8 : ℤ) : ZMod q) := by
  change (((τ' + 8 * (q - 1)) % q : ℕ) : ZMod q) = _
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, cast_qm1]
  push_cast
  ring

theorem cast_zq (x : ℤ) : ((zq q x : ℕ) : ZMod q) = (x : ZMod q) := by
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  change ((Int.toNat (x % (q : ℤ)) : ℕ) : ZMod q) = _
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hq), ZMod.intCast_mod]

theorem eqq_eq (a b : ℕ) : eqq q a b = decide ((a : ZMod q) = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ZMod.natCast_eq_natCast_iff']
  unfold eqq
  rw [Nat.beq_eq]
  exact Iff.rfl

theorem cast_sumR (f : ℕ → ℕ) (m : ℕ) :
    ((sumR q f m : ℕ) : ZMod q) = ∑ i : Fin m, ((f i : ℕ) : ZMod q) := by
  induction m with
  | zero => simp [sumR]
  | succ m ih =>
    change ((addq q (sumR q f m) (f m) : ℕ) : ZMod q) = _
    rw [cast_addq, ih, Fin.sum_univ_castSucc]
    simp

end Res

theorem beqT {a b : ℕ} (h : a = b) : Nat.beq a b = true := by rw [Nat.beq_eq]; exact h

theorem beqF {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · rw [Nat.beq_eq] at hb
    exact absurd hb h

section Formal

variable (q : ℕ) (N : ℕ) (TN : List (List ℕ))

@[expose] noncomputable def dotN (m : ℕ) (a z : List ℕ) : ℕ :=
  sumR q (fun l => mulq q (nth a l) (nth z l)) m

@[expose] noncomputable def reflN (k : ℕ) (z : List ℕ) : List ℕ :=
  ofA (fun l => Bool.rec (nth z l) (subq q (nth z l) (dotN q (N + 1) (nthL TN k) z)) (Nat.beq l k))
    (N + 1) 0

@[expose] noncomputable def wordN (ws : List (Fin N)) (z : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) z (fun k _ acc => reflN q N TN k.val acc) ws

@[expose] noncomputable def unitN (m k : ℕ) : List ℕ :=
  ofA (fun l => Bool.rec 0 1 (Nat.beq l k)) m 0

@[expose] noncomputable def dualAtN (c : List ℕ) (j : ℕ) : ℕ :=
  sumR q (fun o => mulq q (nth c o) (nth (nthL TN o) j)) N

@[expose] noncomputable def dReflN (j : ℕ) (c : List ℕ) : List ℕ :=
  ofA (fun o => Bool.rec (nth c o) (subq q (nth c o) (dualAtN q N TN c j)) (Nat.beq o j)) N 0

@[expose] noncomputable def dWordRevN (ws : List (Fin N)) (c : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) c (fun k _ acc => dReflN q N TN k.val acc) ws

@[expose] noncomputable def FHN (t : Fin N × List (Fin N)) : List ℕ :=
  wordN q N TN t.2 (unitN (N + 1) t.1.val)

@[expose] noncomputable def FCN (t : Fin N × List (Fin N)) : List ℕ :=
  dWordRevN q N TN t.2 (unitN N t.1.val)

@[expose] noncomputable def FAN (t : Fin N × List (Fin N)) (j : ℕ) : ℕ :=
  dotN q (N + 1) (nthL TN j) (FHN q N TN t)

@[expose] noncomputable def rootAtN (c z : List ℕ) : ℕ :=
  sumR q (fun o => mulq q (nth c o) (dotN q (N + 1) (nthL TN o) z)) N

@[expose] noncomputable def matEqF (a b : ℕ → List ℕ) : Bool :=
  allR (fun l => allR (fun m => eqq q (nth (a l) m) (nth (b l) m)) N) N

theorem wordN_append (a b : List (Fin N)) (z : List ℕ) :
    wordN q N TN (a ++ b) z = wordN q N TN a (wordN q N TN b z) := by
  induction a with
  | nil => rfl
  | cons k a ih =>
    rw [List.cons_append]
    change reflN q N TN k.val (wordN q N TN (a ++ b) z) = reflN q N TN k.val (wordN q N TN a _)
    rw [ih]

theorem wordN_wordN (a b : List (Fin N)) (z : List ℕ) :
    wordN q N TN a (wordN q N TN b z) = wordN q N TN (a ++ b) z :=
  (wordN_append q N TN a b z).symm

end Formal

section FormalEq

variable {q : ℕ} [NeZero q] {N : ℕ} {T : Fin N → Vector (ZMod q) (N + 1)} {TN : List (List ℕ)}
  (hT : ∀ (k : Fin N) (l : Fin (N + 1)), (T k).get l = (nth (nthL TN k.val) l.val : ZMod q))
include hT

omit hT in
theorem dot_eq {m : ℕ} {A Z : Vector (ZMod q) (m + 1)} {a z : List ℕ}
    (hA : ∀ l : Fin (m + 1), A.get l = (nth a l.val : ZMod q))
    (hZ : ∀ l : Fin (m + 1), Z.get l = (nth z l.val : ZMod q)) :
    ggFDot A Z = (dotN q (m + 1) a z : ZMod q) := by
  rw [ggFDot, dotN, cast_sumR]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [cast_mulq, hA, hZ]

omit hT in
theorem fUnit_get {M : ℕ} (k l : Fin (M + 1)) :
    (ggFUnit k : Vector (ZMod q) (M + 1)).get l = (nth (unitN (M + 1) k.val) l.val : ZMod q) := by
  rw [ggFUnit, Vector.get_ofFn, unitN, nth, nthD_ofA _ _ _ _ _ l.isLt, zero_add]
  beta_reduce
  by_cases h : l = k
  · rw [if_pos h, beqT (by rw [h])]
    exact Nat.cast_one.symm
  · rw [if_neg h, beqF (fun h' => h (Fin.ext h'))]
    exact Nat.cast_zero.symm

omit hT in
theorem fDUnit_get {M : ℕ} (k l : Fin M) :
    (ggFDUnit k : Vector (ZMod q) M).get l = (nth (unitN M k.val) l.val : ZMod q) := by
  rw [ggFDUnit, Vector.get_ofFn, unitN, nth, nthD_ofA _ _ _ _ _ l.isLt, zero_add]
  beta_reduce
  by_cases h : l = k
  · rw [if_pos h, beqT (by rw [h])]
    exact Nat.cast_one.symm
  · rw [if_neg h, beqF (fun h' => h (Fin.ext h'))]
    exact Nat.cast_zero.symm

theorem refl_get (k : Fin N) {Z : Vector (ZMod q) (N + 1)} {z : List ℕ}
    (hZ : ∀ l : Fin (N + 1), Z.get l = (nth z l.val : ZMod q)) (l : Fin (N + 1)) :
    (ggFRefl T k Z).get l = (nth (reflN q N TN k.val z) l.val : ZMod q) := by
  rw [ggFRefl, Vector.get_ofFn, reflN, nth, nthD_ofA _ _ _ _ _ l.isLt, zero_add]
  beta_reduce
  by_cases h : l = k.castSucc
  · rw [if_pos h, beqT (by rw [h]; rfl)]
    change _ = ((subq q _ _ : ℕ) : ZMod q)
    rw [cast_subq, dot_eq (hT k) hZ, ← hZ l]
  · rw [if_neg h, beqF (fun h' => h (Fin.ext (by rw [h']; rfl)))]
    exact hZ l

theorem word_get (ws : List (Fin N)) {Z : Vector (ZMod q) (N + 1)} {z : List ℕ}
    (hZ : ∀ l : Fin (N + 1), Z.get l = (nth z l.val : ZMod q)) (l : Fin (N + 1)) :
    (ggFWord T ws Z).get l = (nth (wordN q N TN ws z) l.val : ZMod q) := by
  induction ws generalizing l with
  | nil => exact hZ l
  | cons k ws ih => exact refl_get hT k ih l

theorem FH_get (t : Fin N × List (Fin N)) (l : Fin (N + 1)) :
    (ggFH T t).get l = (nth (FHN q N TN t) l.val : ZMod q) :=
  word_get hT t.2 (fun l => fUnit_get t.1.castSucc l) l

theorem dualAt_eq {c : Vector (ZMod q) N} {c' : List ℕ}
    (hc : ∀ o : Fin N, c.get o = (nth c' o.val : ZMod q)) (j : Fin N) :
    ggFDualAt T c j = (dualAtN q N TN c' j.val : ZMod q) := by
  rw [ggFDualAt, dualAtN, cast_sumR]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [cast_mulq, hc, hT, Fin.coe_castSucc]

theorem dRefl_get (j : Fin N) {c : Vector (ZMod q) N} {c' : List ℕ}
    (hc : ∀ o : Fin N, c.get o = (nth c' o.val : ZMod q)) (o : Fin N) :
    (ggFDRefl T j c).get o = (nth (dReflN q N TN j.val c') o.val : ZMod q) := by
  rw [ggFDRefl, Vector.get_ofFn, dReflN, nth, nthD_ofA _ _ _ _ _ o.isLt, zero_add]
  beta_reduce
  by_cases h : o = j
  · rw [if_pos h, beqT (by rw [h])]
    change _ = ((subq q _ _ : ℕ) : ZMod q)
    rw [cast_subq, dualAt_eq hT hc, ← hc o]
  · rw [if_neg h, beqF (fun h' => h (Fin.ext h'))]
    exact hc o

theorem dWordRev_get (ws : List (Fin N)) {c : Vector (ZMod q) N} {c' : List ℕ}
    (hc : ∀ o : Fin N, c.get o = (nth c' o.val : ZMod q)) (o : Fin N) :
    (ggFDWord T ws.reverse c).get o = (nth (dWordRevN q N TN ws c') o.val : ZMod q) := by
  induction ws generalizing o with
  | nil => exact hc o
  | cons k ws ih =>
    rw [List.reverse_cons, ggFDWord, List.foldl_append]
    exact dRefl_get hT k ih o

theorem FC_get (t : Fin N × List (Fin N)) (o : Fin N) :
    (ggFC T t).get o = (nth (FCN q N TN t) o.val : ZMod q) :=
  dWordRev_get hT t.2 (fun o => fDUnit_get t.1 o) o

theorem FA_eq (t : Fin N × List (Fin N)) (j : Fin N) :
    ggFA T t j = (FAN q N TN t j.val : ZMod q) :=
  dot_eq (hT j) (FH_get hT t)

theorem dualAt_FC (t : Fin N × List (Fin N)) (j : Fin N) :
    ggFDualAt T (ggFC T t) j = (dualAtN q N TN (FCN q N TN t) j.val : ZMod q) :=
  dualAt_eq hT (FC_get hT t) j

theorem rootAt_FC_unit (t : Fin N × List (Fin N)) (z : Fin (N + 1)) :
    ggFRootAt T (ggFC T t) (ggFUnit z) =
      (rootAtN q N TN (FCN q N TN t) (unitN (N + 1) z.val) : ZMod q) := by
  rw [ggFRootAt, rootAtN, cast_sumR]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [cast_mulq, FC_get hT, dot_eq (hT o) (fUnit_get z)]

theorem rootAt_eq {c : Vector (ZMod q) N} {c' : List ℕ}
    (hc : ∀ o : Fin N, c.get o = (nth c' o.val : ZMod q)) {Z : Vector (ZMod q) (N + 1)} {z : List ℕ}
    (hZ : ∀ l : Fin (N + 1), Z.get l = (nth z l.val : ZMod q)) :
    ggFRootAt T c Z = (rootAtN q N TN c' z : ZMod q) := by
  rw [ggFRootAt, rootAtN, cast_sumR]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [cast_mulq, hc, dot_eq (hT o) hZ]

end FormalEq

theorem nthD_eq_getD {α : Type} (d : α) (l : List α) (i : ℕ) : nthD d l i = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem getD_nthL (O : List (List ℕ)) (i : ℕ) : O.getD i [] = nthL O i :=
  (nthD_eq_getD [] O i).symm

theorem vec_get {q : ℕ} {n : ℕ} (z : List ℕ) (l : Fin (n + 2)) :
    (ggFVec z : Vector (ZMod q) (n + 2)).get l = (nth z l.val : ZMod q) := by
  rw [ggFVec, Vector.get_ofFn, nth, nthD_eq_getD]

theorem vecEq_decide {R : Type} [DecidableEq R] {m : ℕ} (V W : Vector R m) :
    decide (V = W) = (List.finRange m).all (fun l => decide (V.get l = W.get l)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  refine ⟨fun h l _ => by rw [h]; exact decide_eq_true rfl, fun h => ?_⟩
  exact Vector.ext fun i hi => of_decide_eq_true (h ⟨i, hi⟩ (List.mem_finRange _))

theorem anyR_eq_finRange (p : ℕ → Bool) (m : ℕ) :
    anyR p m = (List.finRange m).any (fun i => p i.val) := by
  rw [Bool.eq_iff_iff, anyR_iff, List.any_eq_true]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, List.mem_finRange _, h⟩, fun ⟨i, _, h⟩ => ⟨i, i.isLt, h⟩⟩

section Q8

variable {q : ℕ} [NeZero q] {n : ℕ} {T : Fin (n + 1) → Vector (ZMod q) (n + 2)} {TN : List (List ℕ)}
  (hT : ∀ (k : Fin (n + 1)) (l : Fin (n + 2)), (T k).get l = (nth (nthL TN k.val) l.val : ZMod q))
include hT

theorem dot_vec (k : Fin (n + 1)) (z : List ℕ) :
    ggFDot (T k) (ggFVec z) = (dotN q (n + 1 + 1) (nthL TN k.val) z : ZMod q) :=
  dot_eq (hT k) (vec_get z)

theorem refl_vec (k : Fin (n + 1)) (z : List ℕ) (l : Fin (n + 2)) :
    (ggFRefl T k (ggFVec z)).get l = (nth (reflN q (n + 1) TN k.val z) l.val : ZMod q) :=
  refl_get hT k (vec_get z) l

theorem rootAt_FC_vec (t : Fin (n + 1) × List (Fin (n + 1))) (z : List ℕ) :
    ggFRootAt T (ggFC T t) (ggFVec z) = (rootAtN q (n + 1) TN (FCN q (n + 1) TN t) z : ZMod q) :=
  rootAt_eq hT (FC_get hT t) (vec_get z)

end Q8

theorem mapEq_decide {α β : Type} [DecidableEq β] (L : List α) (F G : α → α → β) :
    decide ((L.map fun l => L.map fun m => F l m) = (L.map fun l => L.map fun m => G l m)) =
      L.all (fun l => L.all fun m => decide (F l m = G l m)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [List.map_inj_left, List.all_eq_true, decide_eq_true_eq]

section WStar

variable {q : ℕ} [NeZero q] {N : ℕ} {T : Fin N → Vector (ZMod q) (N + 1)} {TN : List (List ℕ)}
  (hT : ∀ (k : Fin N) (l : Fin (N + 1)), (T k).get l = (nth (nthL TN k.val) l.val : ZMod q))
include hT

theorem wordUnit_get (ws : List (Fin N)) (k m : Fin (N + 1)) :
    (ggFWord T ws (ggFUnit k)).get m =
      (nth (wordN q N TN ws (unitN (N + 1) k.val)) m.val : ZMod q) :=
  word_get hT ws (fUnit_get k) m

theorem rootAt_FC_FH (t s : Fin N × List (Fin N)) :
    ggFRootAt T (ggFC T t) (ggFH T s) = (rootAtN q N TN (FCN q N TN t) (FHN q N TN s) : ZMod q) :=
  rootAt_eq hT (FC_get hT t) (FH_get hT s)

theorem matEqF_eq (ws ws' : List (Fin N)) :
    matEqF q N (fun l => wordN q N TN ws (unitN (N + 1) l))
        (fun l => wordN q N TN ws' (unitN (N + 1) l)) =
      decide (ggFMat T ws = ggFMat T ws') := by
  simp only [ggFMat, mapEq_decide, matEqF, allR_eq_finRange, wordUnit_get hT, eqq_eq,
    Fin.coe_castSucc]

end WStar

theorem getD_nth (l : List ℕ) (i : ℕ) : l.getD i 0 = nth l i :=
  (nthD_eq_getD 0 l i).symm

theorem cast_brec {q m : ℕ} (a c : Fin m) :
    (((Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq a.val c.val) : ℕ)) : ZMod q) =
      if a = c then 1 else 0 := by
  by_cases h : a = c
  · rw [if_pos h, beqT (by rw [h])]
    exact Nat.cast_one
  · rw [if_neg h, beqF (fun h' => h (Fin.ext h'))]
    exact Nat.cast_zero

theorem ggGensWord_cons {n : ℕ} (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n))
    (d : Fin n) (gens : List (List GGResLetter)) (i : ℕ) (e : List ℕ) :
    ggGensWord F jl d gens (i :: e) =
      ggResLettersWord F jl d (gens.getD i []) ++ ggGensWord F jl d gens e := by
  simp only [ggGensWord, List.map_cons, List.flatten_cons]

@[expose] noncomputable def gvN (q : ℕ) {n : ℕ} (TN : List (List ℕ))
    (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n)) (d : Fin n)
    (gens : List (List GGResLetter)) (e : List ℕ) (z : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) z
    (fun i _ acc => wordN q (n + 1) TN (ggResLettersWord F jl d (gens.getD i [])) acc) e

theorem gvN_eq (q : ℕ) {n : ℕ} (TN : List (List ℕ)) (F : List (Fin (n + 1) × List (Fin (n + 1))))
    (jl : List (Fin n)) (d : Fin n) (gens : List (List GGResLetter)) (e : List ℕ) (z : List ℕ) :
    gvN q TN F jl d gens e z = wordN q (n + 1) TN (ggGensWord F jl d gens e) z := by
  induction e with
  | nil => rfl
  | cons i e ih =>
    change wordN q (n + 1) TN (ggResLettersWord F jl d (gens.getD i [])) (gvN q TN F jl d gens e z) = _
    rw [ih, ggGensWord_cons, wordN_append]

@[expose] noncomputable def triS (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ℕ) (i k : ℕ) : ℕ :=
  Bool.rec
    (Bool.rec (Bool.rec (Bool.rec a22 a21 (Nat.beq k 1)) a20 (Nat.beq k 0))
      (Bool.rec (Bool.rec a12 a11 (Nat.beq k 1)) a10 (Nat.beq k 0)) (Nat.beq i 1))
    (Bool.rec (Bool.rec a02 a01 (Nat.beq k 1)) a00 (Nat.beq k 0)) (Nat.beq i 0)

@[expose] noncomputable def triLiftN (q : ℕ) (s : ℕ → ℕ → ℕ) : Bool :=
  band (allR (fun i => allR (fun k =>
      decide ((eqq q (s i k) 0 = true) ↔ (eqq q (s k i) 0 = true))) 3) 3)
    (anyR (fun P01 => anyR (fun P02 => anyR (fun P12 => anyR (fun τ' =>
      band (band (band (band (band (band (eqq q P01 (mulq q (s 0 1) (s 1 0)))
        (eqq q P02 (mulq q (s 0 2) (s 2 0)))) (eqq q P12 (mulq q (s 1 2) (s 2 1))))
        (eqq q (tq q τ') (mulq q (mulq q (s 0 1) (s 1 2)) (s 2 0))))
        (eqq q (tq q τ') (mulq q (mulq q (s 0 2) (s 2 1)) (s 1 0))))
        (decide (((τ' : ℤ) - 8) * ((τ' : ℤ) - 8) = (P01 : ℤ) * P02 * P12)))
        (decide (0 ≤ 4 - (P01 : ℤ) - P02 - P12 + ((τ' : ℤ) - 8)))) 17) 5) 5) 5)

theorem triLift_eq {q : ℕ} [NeZero q] (a : Fin 3 → Fin 3 → ZMod q) (s : ℕ → ℕ → ℕ)
    (ha : ∀ i k : Fin 3, a i k = (s i.val k.val : ZMod q)) : ggTriLiftB a = triLiftN q s := by
  have h01 : a 0 1 = (s 0 1 : ZMod q) := ha 0 1
  have h10 : a 1 0 = (s 1 0 : ZMod q) := ha 1 0
  have h02 : a 0 2 = (s 0 2 : ZMod q) := ha 0 2
  have h20 : a 2 0 = (s 2 0 : ZMod q) := ha 2 0
  have h12 : a 1 2 = (s 1 2 : ZMod q) := ha 1 2
  have h21 : a 2 1 = (s 2 1 : ZMod q) := ha 2 1
  unfold ggTriLiftB triLiftN
  rw [band_eq]
  congr 1
  · refine all_finRange _ _ fun i => ?_
    refine all_finRange _ _ fun k => ?_
    simp only [eqq_eq, decide_eq_true_eq, ha, Nat.cast_zero]
  · simp only [any_range, band_eq, eqq_eq, cast_mulq, cast_tq, h01, h10, h02, h20, h12, h21]

section Wit

variable (q : ℕ) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)

@[expose] noncomputable def entryN (u v k l : ℕ) : ℕ :=
  if hk : k < n then
    if hl : l < n then zq q (C ⟨k, hk⟩ ⟨l, hl⟩)
    else if l = n then (if k = ic.val then zq q e₂ else if k = ib.val then v else zq q 0)
    else zq q 0
  else
    if l < n then (if l = ic.val then zq q e₁ else if l = ib.val then u else zq q 0)
    else if l = n then zq q 2
    else zq q 0

@[expose] noncomputable def tableN (u v : ℕ) : List (List ℕ) :=
  ofA (fun k => ofA (entryN q C ib ic e₁ e₂ u v k) (n + 2) 0) (n + 1) 0

@[expose] noncomputable def notPropN (H z : List ℕ) : Bool :=
  anyR (fun l => anyR (fun m =>
    bnot (eqq q (subq q (mulq q (nth H l) (nth z m)) (mulq q (nth H m) (nth z l))) 0)) (n + 1)) (n + 1)

@[expose] noncomputable def q8N (TN : List (List ℕ)) (O : List (List ℕ)) (ci : List (List (ℕ × ℕ)))
    (t : Fin (n + 1) × List (Fin (n + 1))) (x₀ : List ℕ) : Bool :=
  band (band (band (band (band (band (band
    (allR (fun i => eqq q (dotN q (n + 1 + 1) (nthL TN i) x₀) 0) n)
    (anyR (fun l => bnot (eqq q (nth x₀ l) 0)) (n + 1)))
    (decide (n ≤ O.length)))
    (allR (fun k => allR (fun l => eqq q (nth (nthL O k) l) (nth (unitN (n + 1 + 1) k) l)) (n + 2)) n))
    (allR (fun k => allR (fun i => (fun js : ℕ × ℕ => band (decide (js.1 < O.length))
      (allR (fun l => eqq q (nth (reflN q (n + 1) TN k (nthL O i)) l)
        (mulq q js.2 (nth (nthL O js.1) l))) (n + 2)))
      ((ci.getD k []).getD i (0, 0))) O.length) n))
    (decide (t.1.val < n)))
    (eqq q (rootAtN q (n + 1) TN (FCN q (n + 1) TN t) x₀) 0))
    (allR (fun j => notPropN q (n := n) (FHN q (n + 1) TN t) (nthL O j)) O.length)

@[expose] noncomputable def lineN (TN : List (List ℕ)) (allA : Bool) (TT : GGResLineJType)
    (jl : List (Fin n)) (K : List (List ℕ)) (z w : List ℕ)
    (F : List (Fin (n + 1) × List (Fin (n + 1)))) (gens : List (List GGResLetter))
    (elts : List (List ℕ)) : Bool :=
  decide (jl.length = TT.rank) && decide (jl.Nodup) && jl.all (fun j => decide (j ≠ ib)) &&
  (List.finRange n).all (fun j => decide (j = ib) || decide (j ∈ jl)) &&
  (List.finRange TT.rank).all (fun k => (List.finRange TT.rank).all fun l =>
    decide (C (jl.getD k.val ib) (jl.getD l.val ib) = TT.cartan k l)) &&
  allR (fun a => allR (fun c =>
    eqq q (sumR q (fun l => mulq q (nth (nthL TN (jl.getD a ib).val) l) (nth (nthL K l) c)) (n + 1))
      (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq a c))) TT.rank) TT.rank &&
  jl.all (fun j => eqq q (dotN q (n + 1 + 1) (nthL TN j.val) z) 0 &&
    eqq q (dotN q (n + 1 + 1) (nthL TN j.val) w) 0) &&
  anyR (fun i => bnot (eqq q (dotN q (n + 1 + 1) (nthL TN i) z) 0)) n &&
  !F.isEmpty &&
  F.all (fun t => (allA || decide (t.1 ≠ Fin.last n)) &&
    eqq q (rootAtN q (n + 1) TN (FCN q (n + 1) TN t) z) 0 &&
    bnot (eqq q (rootAtN q (n + 1) TN (FCN q (n + 1) TN t) w) 0) &&
    jl.any fun j => bnot (matEqF q (n + 1)
      (fun l => wordN q (n + 1) TN (ggConjWord t ++ [j.castSucc]) (unitN (n + 1 + 1) l))
      (fun l => wordN q (n + 1) TN (j.castSucc :: ggConjWord t) (unitN (n + 1 + 1) l)))) &&
  gens.all (fun ws => ws.all (ggResLetterOk F jl)) &&
  pwN (fun e e' => bnot (matEqF q (n + 1) (fun l => gvN q TN F jl ib gens e (unitN (n + 1 + 1) l))
    (fun l => gvN q TN F jl ib gens e' (unitN (n + 1 + 1) l)))) elts &&
  elts.any (fun e => matEqF q (n + 1) (fun l => gvN q TN F jl ib gens e (unitN (n + 1 + 1) l))
    (fun l => wordN q (n + 1) TN [] (unitN (n + 1 + 1) l))) &&
  (List.range gens.length).all (fun i => elts.all fun e =>
    (elts.any fun e' => matEqF q (n + 1)
      (fun l => gvN q TN F jl ib gens (i :: e) (unitN (n + 1 + 1) l))
      (fun l => gvN q TN F jl ib gens e' (unitN (n + 1 + 1) l))) &&
    (elts.any fun e' => matEqF q (n + 1)
      (fun l => wordN q (n + 1) TN (ggResLettersWord F jl ib (gens.getD i [])).reverse
        (gvN q TN F jl ib gens e (unitN (n + 1 + 1) l)))
      (fun l => gvN q TN F jl ib gens e' (unitN (n + 1 + 1) l)))) &&
  decide (TT.bad ∣ elts.length)

@[expose] noncomputable def witN (u v : ℕ) (w : GGCellWitI n) : Bool :=
  (fun TN : List (List ℕ) => match w with
  | .tv t₁ t₂ l₀ z =>
    (fun H₁ H₂ : List ℕ =>
      band (band (band (allR (fun l =>
          eqq q (subq q (mulq q (nth H₂ l₀.val) (nth H₁ l)) (mulq q (nth H₁ l₀.val) (nth H₂ l))) 0)
          (n + 1)) (bnot (eqq q (nth H₁ l₀.val) 0))) (bnot (eqq q (nth H₂ l₀.val) 0)))
        (bnot (eqq q (subq q
          (mulq q (nth H₁ l₀.val) (rootAtN q (n + 1) TN (FCN q (n + 1) TN t₁) (unitN (n + 2) z.val)))
          (mulq q (nth H₂ l₀.val) (rootAtN q (n + 1) TN (FCN q (n + 1) TN t₂) (unitN (n + 2) z.val))))
          0)))
      (FHN q (n + 1) TN t₁) (FHN q (n + 1) TN t₂)
  | .tvk t₁ t₂ o₀ l =>
    (fun c₁ c₂ : List ℕ =>
      band (band (band (allR (fun o =>
          eqq q (subq q (mulq q (dualAtN q (n + 1) TN c₂ o₀.val) (dualAtN q (n + 1) TN c₁ o))
            (mulq q (dualAtN q (n + 1) TN c₁ o₀.val) (dualAtN q (n + 1) TN c₂ o))) 0) (n + 1))
          (bnot (eqq q (dualAtN q (n + 1) TN c₂ o₀.val) 0)))
          (bnot (eqq q (dualAtN q (n + 1) TN c₁ o₀.val) 0)))
        (bnot (eqq q (subq q (mulq q (dualAtN q (n + 1) TN c₁ o₀.val) (nth (FHN q (n + 1) TN t₁) l.val))
          (mulq q (dualAtN q (n + 1) TN c₂ o₀.val) (nth (FHN q (n + 1) TN t₂) l.val))) 0)))
      (FCN q (n + 1) TN t₁) (FCN q (n + 1) TN t₂)
  | .tri t j' =>
    band (band (inJ ib t.1) (inJ ib j'))
      ((fun P : ℕ => band (band (band (band (bnot (eqq q P 0)) (bnot (eqq q P 1)))
        (bnot (eqq q P 2))) (bnot (eqq q P 3))) (bnot (eqq q P 4)))
        (mulq q (FAN q (n + 1) TN t j'.val) (dualAtN q (n + 1) TN (FCN q (n + 1) TN t) j'.val)))
  | .triple t j' =>
    band (band (band (inJ ib t.1) (inJ ib j')) (decide (5 ≤ q)))
      ((fun s : ℕ → ℕ → ℕ =>
        bnot (eqq q (mulq q (mulq q (s 0 1) (s 1 2)) (s 2 0)) (mulq q (mulq q (s 0 2) (s 2 1)) (s 1 0))))
        ((fun c : List ℕ => (fun d₀ d₁ : ℕ =>
          triS (nth (nthL TN t.1.val) t.1.val) (nth (nthL TN t.1.val) j'.val)
            (FAN q (n + 1) TN t t.1.val) (nth (nthL TN j'.val) t.1.val) (nth (nthL TN j'.val) j'.val)
            (FAN q (n + 1) TN t j'.val) d₀ d₁ (addq q (mulq q d₀ 0) 2))
          (dualAtN q (n + 1) TN c t.1.val) (dualAtN q (n + 1) TN c j'.val)) (FCN q (n + 1) TN t)))
  | .gram t j' =>
    band (band (band (inJ ib t.1) (inJ ib j')) (decide (5 ≤ q)))
      ((fun s : ℕ → ℕ → ℕ =>
        band (bor (bor (bor (band (bnot (eqq q (mulq q (s 1 2) (s 2 1)) 0))
            (bnot (eqq q (mulq q (s 1 2) (s 2 1)) 4)))
          (bnot (eqq q (mulq q (mulq q (s 0 1) (s 1 2)) (s 2 0))
            (mulq q (mulq q (s 0 2) (s 2 1)) (s 1 0)))))
          (band (eqq q (s 1 2) 0) (bnot (eqq q (s 2 1) 0))))
          (band (bnot (eqq q (s 1 2) 0)) (eqq q (s 2 1) 0)))
        (bnot (triLiftN q s)))
        ((fun c : List ℕ => (fun d₀ d₁ : ℕ =>
          triS (nth (nthL TN t.1.val) t.1.val) (nth (nthL TN t.1.val) j'.val)
            (FAN q (n + 1) TN t t.1.val) (nth (nthL TN j'.val) t.1.val) (nth (nthL TN j'.val) j'.val)
            (FAN q (n + 1) TN t j'.val) d₀ d₁ (addq q (mulq q d₀ 0) 2))
          (dualAtN q (n + 1) TN c t.1.val) (dualAtN q (n + 1) TN c j'.val)) (FCN q (n + 1) TN t)))
  | .q8 O ci t x₀ => band (decide (q = 3)) (q8N q TN O ci t x₀)
  | .wstar typ ts d lam gw =>
    (fun t : Fin (n + 1) → Fin (n + 1) × List (Fin (n + 1)) =>
      band (band (band (band (ggWTypeOk typ (n + 1))
        ((List.finRange (n + 1)).all (fun k => band ((gw.getD k.val []).all (fun m => decide (m < n + 1)))
          ((List.finRange (n + 1)).all (fun l => (List.finRange (n + 1)).all fun m =>
            eqq q (nth (wordN q (n + 1) TN [k] (unitN (n + 1 + 1) l.val)) m.val)
              (nth (wordN q (n + 1) TN ((gw.getD k.val []).flatMap fun m =>
                ggConjWord (ts.getD m (0, []))) (unitN (n + 1 + 1) l.val)) m.val))))))
        ((List.finRange (n + 1)).all (fun i => bnot (eqq q (d.getD i.val 0) 0))))
        ((List.finRange (n + 1)).all (fun i => (List.finRange (n + 1)).all fun j =>
          eqq q (mulq q (d.getD i.val 0)
              (rootAtN q (n + 1) TN (FCN q (n + 1) TN (t j)) (FHN q (n + 1) TN (t i))))
            (mulq q (d.getD j.val 0) (zq q (ggWCartanI typ (n + 1) i j))))))
        ((List.finRange (n + 1)).all (fun i => (List.finRange (n + 1)).all fun o =>
          eqq q (sumR q (fun l => mulq q (nth (FHN q (n + 1) TN (t i)) l)
            ((lam.getD l []).getD o.val 0)) (n + 1)) (if i = o then 1 else 0))))
      (fun i => ts.getD i.val (0, []))
  | .line TT jl K z w F gens elts =>
    band (decide (q = 3)) (lineN q C ib TN false TT jl K z w F gens elts)
  | .o2a TT jl K z w F gens elts =>
    band (ggO2aB q C ib ic e₁ e₂ (u : ZMod q) (v : ZMod q))
      (lineN q C ib TN true TT jl K z w F gens elts)
  | w => ggCellWitCheckI q C ib ic e₁ e₂ (u : ZMod q) (v : ZMod q) w)
  (tableN q C ib ic e₁ e₂ u v)

@[expose] noncomputable def cellAtN (wits : List (ℕ × ℕ × GGCellWitI n)) (a b : ℕ) : Bool :=
  match wits.find? (fun w => w.1 == a && w.2.1 == b) with
  | some w => witN q C ib ic e₁ e₂ a b w.2.2
  | none => false

@[expose] noncomputable def ggnCheck (wits : List (ℕ × ℕ × GGCellWitI n)) : Bool :=
  allR (fun a => allR (fun b => cellAtN q C ib ic e₁ e₂ wits a b) q) q

variable {q} [NeZero q]

theorem tab_get (u v : ℕ) (k : Fin (n + 1)) (l : Fin (n + 2)) :
    (ggStdTableI (Int.cast) C ib ic e₁ e₂ (u : ZMod q) (v : ZMod q) k).get l =
      (nth (nthL (tableN q C ib ic e₁ e₂ u v) k.val) l.val : ZMod q) := by
  simp only [ggStdTableI, Vector.get_ofFn, tableN, nthL, nth, nthD_ofA _ _ _ _ _ k.isLt,
    nthD_ofA _ _ _ _ _ l.isLt, zero_add]
  unfold ggStdEntryI entryN
  split_ifs <;> simp only [cast_zq, Int.cast_ofNat, Int.cast_zero]

theorem triMat_eq {N : ℕ} {T : Fin (N + 1) → Vector (ZMod q) (N + 2)} {TN : List (List ℕ)}
    (hT : ∀ (k : Fin (N + 1)) (l : Fin (N + 2)), (T k).get l = (nth (nthL TN k.val) l.val : ZMod q))
    (t : Fin (N + 1) × List (Fin (N + 1))) (j' : Fin (N + 1)) (i k : Fin 3) :
    ggFTriMat T t j' i k = ((fun c : List ℕ => (fun d₀ d₁ : ℕ =>
          triS (nth (nthL TN t.1.val) t.1.val) (nth (nthL TN t.1.val) j'.val)
            (FAN q (N + 1) TN t t.1.val) (nth (nthL TN j'.val) t.1.val) (nth (nthL TN j'.val) j'.val)
            (FAN q (N + 1) TN t j'.val) d₀ d₁ (addq q (mulq q d₀ 0) 2))
          (dualAtN q (N + 1) TN c t.1.val) (dualAtN q (N + 1) TN c j'.val)) (FCN q (N + 1) TN t)
          i.val k.val : ZMod q) := by
  fin_cases i <;> fin_cases k
  · exact hT t.1 t.1.castSucc
  · exact hT t.1 j'.castSucc
  · exact FA_eq hT t t.1
  · exact hT j' t.1.castSucc
  · exact hT j' j'.castSucc
  · exact FA_eq hT t j'
  · exact dualAt_FC hT t t.1
  · exact dualAt_FC hT t j'
  · change ggFDualAt T (ggFC T t) t.1 * 0 + 2 = ((addq q (mulq q _ 0) 2 : ℕ) : ZMod q)
    rw [cast_addq, cast_mulq, dualAt_FC hT t]
    simp

theorem lineN_eq {T : Fin (n + 1) → Vector (ZMod q) (n + 2)} {TN : List (List ℕ)}
    (hT : ∀ (k : Fin (n + 1)) (l : Fin (n + 2)), (T k).get l = (nth (nthL TN k.val) l.val : ZMod q))
    (allA : Bool) (TT : GGResLineJType) (jl : List (Fin n)) (K : List (List ℕ)) (z w : List ℕ)
    (F : List (Fin (n + 1) × List (Fin (n + 1)))) (gens : List (List GGResLetter))
    (elts : List (List ℕ)) :
    lineN q C ib TN allA TT jl K z w F gens elts =
      ggResLineCheck T C ib allA TT jl K z w F gens elts := by
  have hpw := pwN_nodup (fun e => ggFMat T (ggGensWord F jl ib gens e))
    (fun e e' => bnot (matEqF q (n + 1) (fun l => gvN q TN F jl ib gens e (unitN (n + 1 + 1) l))
      (fun l => gvN q TN F jl ib gens e' (unitN (n + 1 + 1) l))))
    (fun e e' => by simp only [gvN_eq, matEqF_eq hT, bnot_eq]) elts
  unfold lineN ggResLineCheck
  rw [hpw]
  simp only [gvN_eq, wordN_wordN, matEqF_eq hT, ggGensWord_cons, bnot_eq, eqq_eq, cast_sumR,
    cast_mulq, cast_brec, getD_nthL, getD_nth, hT, Fin.coe_castSucc, dot_vec hT, rootAt_FC_vec hT,
    Nat.cast_zero, allR_eq_finRange, anyR_eq_finRange, ne_eq, decide_not]

theorem ggnWit_eq (u v : ℕ) (w : GGCellWitI n) :
    witN q C ib ic e₁ e₂ u v w = ggCellWitCheckI q C ib ic e₁ e₂ (u : ZMod q) (v : ZMod q) w := by
  have hT := tab_get (q := q) C ib ic e₁ e₂ u v
  cases w with
  | tv t₁ t₂ l₀ z =>
    simp only [witN, ggCellWitCheckI, FH_get hT, rootAt_FC_unit hT, Fin.coe_castSucc, band_eq,
      bnot_eq, eqq_eq, cast_subq, cast_mulq, Nat.cast_zero, allR_eq_finRange, ne_eq, decide_not]
  | tvk t₁ t₂ o₀ l =>
    simp only [witN, ggCellWitCheckI, FH_get hT, dualAt_FC hT, Fin.coe_castSucc, band_eq,
      bnot_eq, eqq_eq, cast_subq, cast_mulq, Nat.cast_zero, allR_eq_finRange, ne_eq, decide_not]
  | tri t j' =>
    simp only [witN, ggCellWitCheckI, FA_eq hT, dualAt_FC hT, band_eq, bnot_eq, eqq_eq, cast_mulq,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ne_eq, decide_not]
  | triple t j' =>
    simp only [witN, ggCellWitCheckI, triMat_eq hT, band_eq, bnot_eq, eqq_eq, cast_mulq, ne_eq,
      decide_not, Fin.val_zero, Fin.val_one, Fin.val_two]
  | gram t j' =>
    simp only [witN, ggCellWitCheckI, triLift_eq _ _ (triMat_eq hT t j'), band_eq, bor_eq, bnot_eq,
      eqq_eq, cast_mulq, Nat.cast_zero, Nat.cast_ofNat, ne_eq, decide_not, triMat_eq hT, Fin.val_zero,
      Fin.val_one, Fin.val_two]
  | wstar typ ts d lam gw =>
    simp only [witN, ggCellWitCheckI, ggFMat, band_eq, bnot_eq, eqq_eq, cast_mulq, cast_zq,
      cast_sumR, Nat.cast_zero, Nat.cast_ite, Nat.cast_one, ne_eq, decide_not, mapEq_decide,
      wordUnit_get hT, rootAt_FC_FH hT, FH_get hT, Fin.coe_castSucc]
  | std => rfl
  | nospan => rfl
  | q8 O ci t x₀ =>
    simp only [witN, ggCellWitCheckI, ggQ8Check, q8N, notPropN, ggFNotProp, band_eq, bnot_eq,
      eqq_eq, cast_mulq, cast_subq, Nat.cast_zero, allR_eq_finRange, anyR_eq_finRange, ne_eq,
      decide_not, getD_nthL, vecEq_decide, dot_vec hT, refl_vec hT, rootAt_FC_vec hT, FH_get hT,
      vec_get, fUnit_get, Fin.coe_castSucc]
  | line TT jl K z w F gens elts =>
    simp only [witN, ggCellWitCheckI, lineN_eq _ _ hT, band_eq]
  | o2a TT jl K z w F gens elts =>
    simp only [witN, ggCellWitCheckI, lineN_eq _ _ hT, band_eq]
  | o2b => rfl

theorem GGCellCheckI_of_ggn {wits : List (ℕ × ℕ × GGCellWitI n)}
    (h : ggnCheck q C ib ic e₁ e₂ wits = true) : GGCellCheckI q C ib ic e₁ e₂ wits := by
  intro u v
  have hc := (allR_iff _ _).1 ((allR_iff _ _).1 h u.val (ZMod.val_lt u)) v.val (ZMod.val_lt v)
  unfold cellAtN at hc
  unfold ggCellAtI
  cases hf : wits.find? (fun w => w.1 == u.val && w.2.1 == v.val) with
  | none =>
    rw [hf] at hc
    exact absurd hc Bool.false_ne_true
  | some w =>
    rw [hf] at hc
    have hc' : witN q C ib ic e₁ e₂ u.val v.val w.2.2 = true := hc
    have e := ggnWit_eq (q := q) C ib ic e₁ e₂ u.val v.val w.2.2
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at e
    change ggCellWitCheckI q C ib ic e₁ e₂ u v w.2.2 = true
    rw [← e]
    exact hc'

noncomputable instance (priority := high) ggnDecCell
    (wits : List (ℕ × ℕ × GGCellWitI n)) :
    Decidable (∀ u v : ZMod q, ggCellAtI q C ib ic e₁ e₂ wits u v = true) :=
  if h : ggnCheck q C ib ic e₁ e₂ wits = true then isTrue (GGCellCheckI_of_ggn C ib ic e₁ e₂ h)
  else Fintype.decidableForallFintype

end Wit

end CFSG.StandardType.GGCellN
