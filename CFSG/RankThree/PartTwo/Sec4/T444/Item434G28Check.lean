module

public import CFSG.Quasithin.Recognition.CertF8
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Quasithin

theorem ofNat'_toNat' (a : GF8) : GF8.ofNat' a.toNat = a := by
  obtain ⟨⟨v, hv⟩⟩ := a
  simp only [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hv]

theorem toNat_lt' (a : GF8) : a.toNat < 8 := a.val.isLt

theorem ofNat'_mulNat' {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    GF8.ofNat' (GF8.mulNat a b) = GF8.ofNat' a * GF8.ofNat' b := by
  show _ = GF8.ofNat' (GF8.mulNat (GF8.ofNat' a).toNat (GF8.ofNat' b).toNat)
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem mulNat_lt' {a b : ℕ} (ha : a < 8) (hb : b < 8) : GF8.mulNat a b < 8 := by
  have h : ∀ a : Fin 8, ∀ b : Fin 8, GF8.mulNat a b < 8 := by decide
  exact h ⟨a, ha⟩ ⟨b, hb⟩

theorem xor_lt8' {a b : ℕ} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 :=
  Nat.xor_lt_two_pow (n := 3) ha hb

theorem ofNat'_xor' {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    GF8.ofNat' (a ^^^ b) = GF8.ofNat' a + GF8.ofNat' b := by
  show _ = GF8.ofNat' ((GF8.ofNat' a).toNat ^^^ (GF8.ofNat' b).toNat)
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat'_xor6 {t0 t1 t2 t3 t4 t5 : ℕ} (h0 : t0 < 8) (h1 : t1 < 8) (h2 : t2 < 8)
    (h3 : t3 < 8) (h4 : t4 < 8) (h5 : t5 < 8) :
    GF8.ofNat' (t0 ^^^ t1 ^^^ t2 ^^^ t3 ^^^ t4 ^^^ t5) =
      GF8.ofNat' t0 + GF8.ofNat' t1 + GF8.ofNat' t2 + GF8.ofNat' t3 + GF8.ofNat' t4 +
        GF8.ofNat' t5 := by
  have h01 := xor_lt8' h0 h1
  have h012 := xor_lt8' h01 h2
  have h0123 := xor_lt8' h012 h3
  have h01234 := xor_lt8' h0123 h4
  rw [ofNat'_xor' h01234 h5, ofNat'_xor' h0123 h4, ofNat'_xor' h012 h3, ofNat'_xor' h01 h2,
    ofNat'_xor' h0 h1]

theorem ofNat'_eq_zero_iff' {x : ℕ} (hx : x < 8) : GF8.ofNat' x = 0 ↔ x = 0 := by
  show GF8.ofNat' x = GF8.ofNat' 0 ↔ x = 0
  simp [GF8.ofNat', Nat.mod_eq_of_lt hx]

theorem ofNat'_inj' {x y : ℕ} (hx : x < 8) (hy : y < 8) (h : GF8.ofNat' x = GF8.ofNat' y) :
    x = y := by
  simp only [GF8.ofNat', GF8.mk.injEq, Fin.mk.injEq, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy] at h
  exact h

theorem getElem!_ofFn_nat' {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]


@[expose] def idCode : Array ℕ :=
  Array.ofFn (n := 36) fun t => if t.val / 6 = t.val % 6 then 1 else 0

@[expose] def mulTab : Array ℕ := Array.ofFn (n := 64) fun t => GF8.mulNat (t.val / 8) (t.val % 8)

@[expose] def mt (a b : ℕ) : ℕ := mulTab[8 * a + b]!

@[expose] def mulEntry (A B : Array ℕ) (i j : ℕ) : ℕ :=
  mt A[6 * i]! B[j]! ^^^ mt A[6 * i + 1]! B[6 + j]! ^^^ mt A[6 * i + 2]! B[12 + j]! ^^^
    mt A[6 * i + 3]! B[18 + j]! ^^^ mt A[6 * i + 4]! B[24 + j]! ^^^ mt A[6 * i + 5]! B[30 + j]!

@[expose] def mulCode (A B : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 36) fun t => mulEntry A B (t.val / 6) (t.val % 6)

theorem mt_eq {a b : ℕ} (ha : a < 8) (hb : b < 8) : mt a b = GF8.mulNat a b := by
  rw [mt, mulTab, getElem!_ofFn_nat' _ (by omega)]
  have h1 : (8 * a + b) / 8 = a := by omega
  have h2 : (8 * a + b) % 8 = b := by omega
  simp only [h1, h2]

theorem mt_lt {a b : ℕ} (ha : a < 8) (hb : b < 8) : mt a b < 8 := by
  rw [mt_eq ha hb]
  exact mulNat_lt' ha hb

theorem ofNat'_mt {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    GF8.ofNat' (mt a b) = GF8.ofNat' a * GF8.ofNat' b := by
  rw [mt_eq ha hb]
  exact ofNat'_mulNat' ha hb

@[expose] def decode (A : Array ℕ) : Matrix (Fin 6) (Fin 6) GF8 :=
  Matrix.of fun i j => GF8.ofNat' A[6 * i.val + j.val]!

@[expose] def Valid (A : Array ℕ) : Prop := A.size = 36 ∧ ∀ i < 36, A[i]! < 8

instance (A : Array ℕ) : Decidable (Valid A) := by unfold Valid; infer_instance

theorem valid_idCode : Valid idCode := by
  refine ⟨by simp [idCode], fun i hi => ?_⟩
  rw [idCode, getElem!_ofFn_nat' _ hi]
  split_ifs <;> norm_num

theorem valid_mulCode {A B : Array ℕ} (hA : Valid A) (hB : Valid B) : Valid (mulCode A B) := by
  refine ⟨by simp [mulCode], fun t ht => ?_⟩
  rw [mulCode, getElem!_ofFn_nat' _ ht]
  simp only [mulEntry]
  have l : ∀ a b : ℕ, a < 36 → b < 36 → mt A[a]! B[b]! < 8 := fun a b ha hb =>
    mt_lt (hA.2 a ha) (hB.2 b hb)
  exact xor_lt8' (xor_lt8' (xor_lt8' (xor_lt8' (xor_lt8' (l _ _ (by omega) (by omega))
    (l _ _ (by omega) (by omega))) (l _ _ (by omega) (by omega))) (l _ _ (by omega) (by omega)))
    (l _ _ (by omega) (by omega))) (l _ _ (by omega) (by omega))

theorem decode_mulCode {A B : Array ℕ} (hA : Valid A) (hB : Valid B) :
    decode (mulCode A B) = decode A * decode B := by
  ext i j
  have hi := i.2
  have hj := j.2
  have hlt : ∀ a b : ℕ, a < 36 → b < 36 → mt A[a]! B[b]! < 8 := fun a b ha hb =>
    mt_lt (hA.2 a ha) (hB.2 b hb)
  have e1 : (6 * i.val + j.val) / 6 = i.val := by omega
  have e2 : (6 * i.val + j.val) % 6 = j.val := by omega
  simp only [decode, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_six]
  rw [mulCode, getElem!_ofFn_nat' _ (by omega : 6 * i.val + j.val < 36)]
  simp only [e1, e2, mulEntry]
  rw [ofNat'_xor6 (hlt _ _ (by omega) (by omega)) (hlt _ _ (by omega) (by omega))
    (hlt _ _ (by omega) (by omega)) (hlt _ _ (by omega) (by omega))
    (hlt _ _ (by omega) (by omega)) (hlt _ _ (by omega) (by omega))]
  rw [ofNat'_mt (hA.2 _ (by omega)) (hB.2 _ (by omega)),
    ofNat'_mt (hA.2 _ (by omega)) (hB.2 _ (by omega)),
    ofNat'_mt (hA.2 _ (by omega)) (hB.2 _ (by omega)),
    ofNat'_mt (hA.2 _ (by omega)) (hB.2 _ (by omega)),
    ofNat'_mt (hA.2 _ (by omega)) (hB.2 _ (by omega)),
    ofNat'_mt (hA.2 _ (by omega)) (hB.2 _ (by omega))]
  simp

theorem decode_idCode : decode idCode = 1 := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [decode, Matrix.of_apply, Matrix.one_apply]
  rw [idCode, getElem!_ofFn_nat' _ (by omega : 6 * i.val + j.val < 36)]
  have e1 : (6 * i.val + j.val) / 6 = i.val := by omega
  have e2 : (6 * i.val + j.val) % 6 = j.val := by omega
  simp only [e1, e2]
  by_cases h : i = j
  · subst h
    simp [GF8.ofNat']
    rfl
  · have hne : i.val ≠ j.val := fun hh => h (Fin.ext hh)
    simp [h, hne]
    rfl

theorem eq_of_decode_eq {A B : Array ℕ} (hA : Valid A) (hB : Valid B)
    (h : decode A = decode B) : A = B := by
  apply Array.ext (by rw [hA.1, hB.1])
  intro t ht1 ht2
  have ht : t < 36 := hA.1 ▸ ht1
  have hi : t / 6 < 6 := by omega
  have hj : t % 6 < 6 := by omega
  have := congrFun (congrFun h ⟨t / 6, hi⟩) ⟨t % 6, hj⟩
  simp only [decode, Matrix.of_apply] at this
  have ht' : 6 * (t / 6) + t % 6 = t := by omega
  simp only [ht'] at this
  have := ofNat'_inj' (hA.2 t ht) (hB.2 t ht) this
  rw [getElem!_pos A t (by omega), getElem!_pos B t (by omega)] at this
  exact this

@[expose] def rootEntries : ℕ → List (ℕ × ℕ × ℕ)
  | 0 => [(0, 3, 2), (4, 2, 1), (5, 1, 1)]
  | 1 => [(0, 2, 1), (5, 3, 1)]
  | 2 => [(0, 4, 1), (1, 3, 1), (5, 2, 2)]
  | 3 => [(1, 2, 1), (5, 4, 1)]
  | 4 => [(1, 4, 2), (3, 2, 1), (5, 0, 1)]
  | 5 => [(1, 0, 1), (3, 4, 1)]
  | 6 => [(1, 5, 1), (2, 4, 1), (3, 0, 2)]
  | 7 => [(2, 0, 1), (3, 5, 1)]
  | 8 => [(2, 5, 2), (3, 1, 1), (4, 0, 1)]
  | 9 => [(2, 1, 1), (4, 5, 1)]
  | 10 => [(0, 5, 1), (2, 3, 1), (4, 1, 2)]
  | 11 => [(0, 1, 1), (4, 3, 1)]
  | _ => []

@[expose] def rootEntry {F : Type*} [CommRing F] (r : ℕ) (t : F) (i j : Fin 6) : F :=
  (if i = j then 1 else 0) +
    ((rootEntries r).map fun e : ℕ × ℕ × ℕ =>
      if i.val = e.1 ∧ j.val = e.2.1 then (if e.2.2 = 1 then t else t * t) else 0).sum

@[expose] def rootMatrix {F : Type*} [CommRing F] (r : ℕ) (t : F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of (rootEntry r t)

@[expose] def rootCode (r t : ℕ) : Array ℕ :=
  (rootEntries r).foldl (fun A e => A.set! (6 * e.1 + e.2.1)
    (A[6 * e.1 + e.2.1]! ^^^ (if e.2.2 = 1 then t else GF8.mulNat t t))) idCode

@[expose] def letterCode (n : ℕ) : Array ℕ := rootCode ((n / 8) % 12) (n % 8)

@[expose] def wordCode (w : List ℕ) : Array ℕ :=
  w.foldl (fun A n => mulCode A (letterCode n)) idCode

@[expose] def powCode (A : Array ℕ) : ℕ → Array ℕ
  | 0 => idCode
  | k + 1 => mulCode (powCode A k) A

theorem decode_rootCode_apply : ∀ r : Fin 12, ∀ t : Fin 8, ∀ i j : Fin 6,
    GF8.ofNat' (rootCode r t)[6 * i.val + j.val]! = rootEntry r (GF8.ofNat' t) i j := by
  decide +kernel

theorem decode_rootCode (r t : ℕ) (hr : r < 12) (ht : t < 8) :
    decode (rootCode r t) = rootMatrix r (GF8.ofNat' t) :=
  Matrix.ext fun i j => decode_rootCode_apply ⟨r, hr⟩ ⟨t, ht⟩ i j

theorem lt_rootCode : ∀ r : Fin 12, ∀ t : Fin 8, ∀ i : Fin 36, (rootCode r t)[i.val]! < 8 := by
  decide +kernel

theorem size_rootCode : ∀ r : Fin 12, ∀ t : Fin 8, (rootCode r t).size = 36 := by
  decide +kernel

theorem valid_rootCode (r t : ℕ) (hr : r < 12) (ht : t < 8) : Valid (rootCode r t) :=
  ⟨size_rootCode ⟨r, hr⟩ ⟨t, ht⟩, fun i hi => lt_rootCode ⟨r, hr⟩ ⟨t, ht⟩ ⟨i, hi⟩⟩

theorem valid_letterCode (n : ℕ) : Valid (letterCode n) :=
  valid_rootCode _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))

theorem valid_foldl_letterCode (w : List ℕ) {A : Array ℕ} (hA : Valid A) :
    Valid (w.foldl (fun A n => mulCode A (letterCode n)) A) := by
  induction w generalizing A with
  | nil => exact hA
  | cons n w ih =>
    rw [List.foldl_cons]
    exact ih (valid_mulCode hA (valid_letterCode n))

theorem valid_wordCode (w : List ℕ) : Valid (wordCode w) :=
  valid_foldl_letterCode w valid_idCode

@[expose] def invWordCode (w : List ℕ) : Array ℕ := wordCode w.reverse

@[expose] def t3List (U Z O : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 243) fun t => mulCode (mulCode (powCode U (t.val / 27))
    (powCode Z ((t.val / 3) % 9))) (powCode O (t.val % 3))

@[expose] def e0List (u z : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 9) fun t => mulCode (powCode u (t.val / 3)) (powCode z (t.val % 3))

@[expose] def t3OK (L : Array (Array ℕ)) : Bool :=
  L.size == 243 && L[0]! == idCode &&
  (List.range 243).all (fun i => (List.range i).all fun j => L[i]! != L[j]!) &&
  (List.range 243).all (fun i => (List.range 243).all fun j => L.contains (mulCode L[i]! L[j]!)) &&
  (List.range 243).all (fun i => (List.range 243).any fun j => mulCode L[i]! L[j]! == idCode)

@[expose] def goodPair (a b : Array ℕ) : Bool :=
  a != idCode && b != idCode && b != a && mulCode a b == mulCode b a &&
    powCode a 3 == idCode && powCode b 3 == idCode && b != mulCode a a

@[expose] def conjOK (L E0 gs gis : Array (Array ℕ)) : Bool :=
  (List.range gs.size).all (fun v => mulCode gs[v]! gis[v]! == idCode) &&
  (List.range 243).all fun i => (List.range 243).all fun j =>
    !goodPair L[i]! L[j]! || (List.range gs.size).any fun v =>
      E0.contains (mulCode (mulCode gs[v]! L[i]!) gis[v]!) &&
        E0.contains (mulCode (mulCode gs[v]! L[j]!) gis[v]!)

@[expose] def genOK (u z : Array ℕ) (genW : Array (List ℕ)) (tn : Array ℕ) (ts : Array (List ℕ)) :
    Bool :=
  u != idCode && z != idCode && genW.size == 30 &&
  (List.range 14).all (fun k => mulCode (wordCode genW[k]!) z == mulCode z (wordCode genW[k]!)) &&
  (List.range 16).all (fun k =>
    mulCode (wordCode genW[14 + k]!) u == mulCode u (wordCode genW[14 + k]!)) &&
  tn.size == ts.size &&
  (List.range ts.size).all fun m => (ts[m]!).all (· < 30) &&
    wordCode ((ts[m]!).flatMap fun i => genW[i]!) == letterCode tn[m]!

theorem valid_powCode {A : Array ℕ} (hA : Valid A) (k : ℕ) : Valid (powCode A k) := by
  induction k with
  | zero => exact valid_idCode
  | succ k ih => exact valid_mulCode ih hA

theorem getElem!_t3List (U Z O : Array ℕ) {i : ℕ} (hi : i < 243) :
    (t3List U Z O)[i]! =
      mulCode (mulCode (powCode U (i / 27)) (powCode Z ((i / 3) % 9))) (powCode O (i % 3)) := by
  rw [t3List, getElem!_ofFn_nat' _ hi]

theorem valid_t3List {U Z O : Array ℕ} (hU : Valid U) (hZ : Valid Z) (hO : Valid O) {i : ℕ}
    (hi : i < 243) : Valid (t3List U Z O)[i]! := by
  rw [getElem!_t3List U Z O hi]
  exact valid_mulCode (valid_mulCode (valid_powCode hU _) (valid_powCode hZ _))
    (valid_powCode hO _)

theorem getElem!_e0List (u z : Array ℕ) {i : ℕ} (hi : i < 9) :
    (e0List u z)[i]! = mulCode (powCode u (i / 3)) (powCode z (i % 3)) := by
  rw [e0List, getElem!_ofFn_nat' _ hi]

theorem valid_e0List {u z : Array ℕ} (hu : Valid u) (hz : Valid z) {i : ℕ} (hi : i < 9) :
    Valid (e0List u z)[i]! := by
  rw [getElem!_e0List u z hi]
  exact valid_mulCode (valid_powCode hu _) (valid_powCode hz _)

theorem size_t3List (U Z O : Array ℕ) : (t3List U Z O).size = 243 := by simp [t3List]

theorem size_e0List (u z : Array ℕ) : (e0List u z).size = 9 := by simp [e0List]

theorem t3OK_spec {L : Array (Array ℕ)} (h : t3OK L = true) :
    L.size = 243 ∧ L[0]! = idCode ∧ (∀ i < 243, ∀ j < i, L[i]! ≠ L[j]!) ∧
    (∀ i < 243, ∀ j < 243, ∃ k < 243, mulCode L[i]! L[j]! = L[k]!) ∧
    (∀ i < 243, ∃ j < 243, mulCode L[i]! L[j]! = idCode) := by
  simp only [t3OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, List.any_eq_true, Array.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨hsz, h0⟩, hd⟩, hm⟩, hi⟩ := h
  refine ⟨hsz, h0, fun i hi' j hj => hd i hi' j hj, fun i hi' j hj => ?_, fun i hi' => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Array.mem_iff_getElem.mp (hm i hi' j hj)
    exact ⟨k, hsz ▸ hk, by rw [getElem!_pos L k hk, hk']⟩
  · obtain ⟨j, hj, hj'⟩ := hi i hi'
    exact ⟨j, hj, hj'⟩

theorem goodPair_of {a b : Array ℕ} (h1 : a ≠ idCode) (h2 : powCode a 3 = idCode)
    (h3 : powCode b 3 = idCode) (h4 : mulCode a b = mulCode b a) (h5 : b ≠ idCode) (h6 : b ≠ a)
    (h7 : b ≠ mulCode a a) : goodPair a b = true := by
  simp [goodPair, h1, h2, h3, h4, h5, h6, h7]

theorem goodPair_spec {a b : Array ℕ} (h : goodPair a b = true) :
    a ≠ idCode ∧ powCode a 3 = idCode ∧ powCode b 3 = idCode ∧ mulCode a b = mulCode b a ∧
      b ≠ idCode ∧ b ≠ a ∧ b ≠ mulCode a a := by
  simp only [goodPair, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h5⟩, h6⟩, h4⟩, h2⟩, h3⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem conjOK_spec {L E0 gs gis : Array (Array ℕ)} (h : conjOK L E0 gs gis = true) :
    (∀ v < gs.size, mulCode gs[v]! gis[v]! = idCode) ∧
    ∀ i < 243, ∀ j < 243, goodPair L[i]! L[j]! = true → ∃ v < gs.size,
      (∃ m < E0.size, mulCode (mulCode gs[v]! L[i]!) gis[v]! = E0[m]!) ∧
      (∃ m < E0.size, mulCode (mulCode gs[v]! L[j]!) gis[v]! = E0[m]!) := by
  simp only [conjOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Array.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun v hv => h1 v hv, fun i hi j hj hg => ?_⟩
  rcases h2 i hi j hj with h | ⟨v, hv, ha, hb⟩
  · rw [hg] at h
    exact absurd h (by simp)
  · refine ⟨v, hv, ?_, ?_⟩
    · obtain ⟨m, hm, hm'⟩ := Array.mem_iff_getElem.mp ha
      exact ⟨m, hm, by rw [getElem!_pos E0 m hm, hm']⟩
    · obtain ⟨m, hm, hm'⟩ := Array.mem_iff_getElem.mp hb
      exact ⟨m, hm, by rw [getElem!_pos E0 m hm, hm']⟩

theorem genOK_spec {u z : Array ℕ} {genW : Array (List ℕ)} {tn : Array ℕ} {ts : Array (List ℕ)}
    (h : genOK u z genW tn ts = true) :
    u ≠ idCode ∧ z ≠ idCode ∧ genW.size = 30 ∧
    (∀ k < 14, mulCode (wordCode genW[k]!) z = mulCode z (wordCode genW[k]!)) ∧
    (∀ k < 16, mulCode (wordCode genW[14 + k]!) u = mulCode u (wordCode genW[14 + k]!)) ∧
    tn.size = ts.size ∧
    ∀ m < ts.size, (∀ i ∈ ts[m]!, i < 30) ∧
      wordCode ((ts[m]!).flatMap fun i => genW[i]!) = letterCode tn[m]! := by
  simp only [genOK, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, hz⟩, hsz⟩, ha⟩, hb⟩, hts⟩, hm⟩ := h
  refine ⟨hu, hz, hsz, ha, hb, hts, fun m hm' => ?_⟩
  obtain ⟨h1, h2⟩ := hm m hm'
  exact ⟨h1, h2⟩

end CFSG.RankThree.PartTwo.Sec4.Item434G28
