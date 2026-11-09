module

public import CFSG.Sporadic.Co2Jc.Native.Cocycle
public import Certificates.Kernel.Co2Jc.Gen

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native CFSG.Sporadic.Co2Jc.Data

@[expose] noncomputable def wordActK (w : List Nat) (m : Nat) : Nat := w.foldr (fun k acc => njK k acc) m

@[expose] noncomputable def rowOfK : List Nat → Nat → Nat
  | [], _ => 0
  | k :: w, m => rowOfK w m ^^^ (wordActK w m <<< (10 * k))

@[expose] noncomputable def rowStepK (k : Nat) (first tail : List Nat) : List Nat :=
  ten.map fun rho =>
    first[rho]! ^^^
      ten.foldr
        (fun rhop acc => if (njK k (2 ^ rhop)).testBit rho then tail[rhop]! ^^^ acc else acc) 0

@[expose] noncomputable def preMaskK (k rho v : Nat) : Nat :=
  ten.foldr
    (fun b acc => Bool.rec acc ((2 ^ (100 * k + 10 * b + rho)) ^^^ acc)
      (Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1)) 0

@[expose] noncomputable def preMaskVecK (k v : Nat) : List Nat :=
  ten.map fun rho => preMaskK k rho v

@[expose] noncomputable def rowAllK : List Nat → Nat → List Nat
  | [], _ => List.replicate 10 0
  | k :: w, j => rowStepK k (preMaskVecK k (wordActK w (2 ^ j))) (rowAllK w j)

@[expose] noncomputable def dualRowsK : List Nat :=
  rels.flatMap fun r => (List.range 10).map fun j => rowOfK r (2 ^ j)

@[expose] noncomputable def rowActK : List Nat → Nat → List Nat × Nat
  | [], j => (List.replicate 10 0, 2 ^ j)
  | k :: w, j => (rowStepK k (preMaskVecK k (rowActK w j).2) (rowActK w j).1, njK k (rowActK w j).2)

@[expose] noncomputable def splitRowsK : List Nat :=
  rels.flatMap fun r => (List.range 10).flatMap fun j => (rowActK r j).1

theorem gl_eq (k x : Nat) : gl k x = njK k x := glNJT_eq_njK k x

theorem wordActK_eq (w : List Nat) (m : Nat) : CFSG.Sporadic.Co2Jc.wordAct w m = wordActK w m :=
  wordAct_eq w m

theorem rowOf_eq (w : List Nat) (m : Nat) : rowOf w m = rowOfK w m := by
  induction w with
  | nil => rfl
  | cons k w ih => rw [rowOf, rowOfK, ih, wordActK_eq]

theorem rowStep_eq (k : Nat) (first tail : List Nat) :
    rowStep k first tail = rowStepK k first tail := by
  simp only [rowStep, rowStepK, gl_eq]

theorem bit_beq (v b : Nat) : Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1 = v.testBit b := by
  rw [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ b) with h | h <;> simp [h] <;> rfl

theorem preMaskVec_eq (k v : Nat) : preMaskVec k v = preMaskVecK k v := by
  simp only [preMaskVec, preMaskVecK, preMask, preMaskK, bit_beq]
  congr
  funext rho
  congr
  funext b acc
  cases v.testBit b <;> rfl

theorem rowAll_eq (w : List Nat) (j : Nat) : rowAll w j = rowAllK w j := by
  induction w with
  | nil => rfl
  | cons k w ih => rw [rowAll, rowAllK, ih, wordActK_eq, rowStep_eq, preMaskVec_eq]

theorem dualRows_eq : dualRows = dualRowsK := by
  simp only [dualRows, dualRowsK, rowOf_eq]

theorem rowActK_eq (j : Nat) : ∀ w, rowActK w j = (rowAllK w j, wordActK w (2 ^ j))
  | [] => rfl
  | k :: w => by
    rw [rowActK, rowActK_eq j w, rowAllK]
    rfl

theorem splitRows_eq : splitRows = splitRowsK := by
  simp only [splitRows, splitRowsK, rowAll_eq, rowActK_eq]

@[expose] noncomputable def relRows (r : List Nat) : List Nat :=
  (List.range 10).flatMap fun j => (rowActK r j).1

@[expose] noncomputable def relRowsJ (r : List Nat) (lo m : Nat) : List Nat :=
  (List.range' lo m).flatMap fun j => (rowActK r j).1

theorem relRows_split (r : List Nat) : relRows r = relRowsJ r 0 5 ++ relRowsJ r 5 5 := by
  have e : List.range 10 = List.range' 0 5 ++ List.range' 5 5 := rfl
  rw [relRows, e, List.flatMap_append]
  rfl

theorem eq_of_halves {a b L : List Nat} (h1 : (a == L.take 50) = true)
    (h2 : (b == L.drop 50) = true) : a ++ b = L := by
  rw [eq_of_beq h1, eq_of_beq h2, List.take_append_drop]

theorem flatMap_range_getElem! (f : List Nat → List Nat) :
    ∀ L : List (List Nat), L.flatMap f = (List.range L.length).flatMap fun i => f L[i]!
  | [] => rfl
  | a :: L => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_map, flatMap_range_getElem! f L]
    simp

theorem flatMap_congr_mem {f g : Nat → List Nat} :
    ∀ l : List Nat, (∀ i ∈ l, f i = g i) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons.2 (Or.inl rfl)),
      flatMap_congr_mem l fun i hi => h i (List.mem_cons_of_mem a hi)]

theorem splitRowsK_eq_of (D : List (List Nat)) (h : ∀ i < 25, relRows rels[i]! = D[i]!) :
    splitRowsK = (List.range 25).flatMap fun i => D[i]! := by
  have e : splitRowsK = rels.flatMap relRows := rfl
  have hl : rels.length = 25 := rfl
  rw [e, flatMap_range_getElem!, hl]
  exact flatMap_congr_mem _ fun i hi => h i (List.mem_range.1 hi)

@[expose] noncomputable def parS (k : Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.xor ih (Nat.land (Nat.shiftRight x i) 1)) k

@[expose] noncomputable def splitSolK : Bool :=
  splitRowsK.all fun r => parS 300 (Nat.land r gamma0) == 0

@[expose] noncomputable def xorRowsS (rows : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih m => Bool.rec (ih (Nat.shiftRight m 1)) (Nat.xor r (ih (Nat.shiftRight m 1)))
      (Nat.beq (Nat.land m 1) 1)) rows

@[expose] noncomputable def splitMaskC (lo : Nat) : Bool :=
  (List.range' lo 30).all fun u => xorRowsS splitRowsK (combSplit[u]!) == splitRes u

theorem shiftRight_land_one (x i : Nat) :
    Nat.land (Nat.shiftRight x i) 1 = if x.testBit i then 1 else 0 := by
  rw [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem parS_eq (x : Nat) : ∀ k, parS k x =
    (List.range k).foldl (fun acc i => if x.testBit i then acc ^^^ 1 else acc) 0
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← parS_eq x k]
    change Nat.xor (parS k x) (Nat.land (Nat.shiftRight x k) 1) = _
    rw [shiftRight_land_one]
    cases x.testBit k
    · simp
    · simp

theorem dot_eq (a b : Nat) : dot a b = parS 300 (Nat.land a b) := by
  rw [parS_eq, dot]
  simp only [Nat.land_eq, Nat.testBit_and]

theorem all_range_getElem! (f : Nat → Bool) (L : List Nat) :
    (List.range L.length).all (fun i => f L[i]!) = L.all f := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := h i hi
    rwa [getElem!_pos L i hi] at this
  · intro h i hi
    rw [getElem!_pos L i hi]
    exact h _ (List.getElem_mem hi)

theorem splitSol_eq (hl : splitRowsK.length = 2500) : splitSolOK = splitSolK := by
  rw [splitSolOK, splitSolK, splitRows_eq,
    ← all_range_getElem! (fun r => parS 300 (Nat.land r gamma0) == 0) splitRowsK, hl]
  simp only [dot_eq]

theorem parS_zero_arg : ∀ k, parS k 0 = 0
  | 0 => rfl
  | k + 1 => by
    change Nat.xor (parS k 0) (Nat.land (Nat.shiftRight 0 k) 1) = 0
    rw [parS_zero_arg k]
    simp only [Nat.xor_eq, Nat.land_eq, Nat.shiftRight_eq', Nat.zero_shiftRight, Nat.zero_and,
      Nat.xor_zero]

theorem parS_add (a x : Nat) : ∀ b, parS (a + b) x = Nat.xor (parS a x) (parS b (x >>> a))
  | 0 => (Nat.xor_zero _).symm
  | b + 1 => by
    change Nat.xor (parS (a + b) x) (Nat.land (Nat.shiftRight x (a + b)) 1) =
      Nat.xor (parS a x) (Nat.xor (parS b (x >>> a)) (Nat.land (Nat.shiftRight (x >>> a) b) 1))
    rw [parS_add a x b]
    have e : Nat.shiftRight x (a + b) = Nat.shiftRight (x >>> a) b := by
      simp only [Nat.shiftRight_eq', Nat.shiftRight_add]
    rw [e]
    exact Nat.xor_assoc _ _ _

theorem parS_xor (x y : Nat) : ∀ k, parS k (x ^^^ y) = Nat.xor (parS k x) (parS k y)
  | 0 => (Nat.xor_zero 0).symm
  | k + 1 => by
    change Nat.xor (parS k (x ^^^ y)) (Nat.land (Nat.shiftRight (x ^^^ y) k) 1) =
      Nat.xor (Nat.xor (parS k x) (Nat.land (Nat.shiftRight x k) 1))
        (Nat.xor (parS k y) (Nat.land (Nat.shiftRight y k) 1))
    rw [parS_xor x y k]
    have e : Nat.land (Nat.shiftRight (x ^^^ y) k) 1 =
        Nat.xor (Nat.land (Nat.shiftRight x k) 1) (Nat.land (Nat.shiftRight y k) 1) := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.land_eq, Nat.xor_eq, Nat.shiftRight_eq', Nat.testBit_and, Nat.testBit_xor,
        Nat.testBit_shiftRight]
      cases (1 : Nat).testBit i <;> simp
    rw [e]
    change (parS k x ^^^ parS k y) ^^^ (_ ^^^ _) = (parS k x ^^^ _) ^^^ (parS k y ^^^ _)
    ac_rfl

theorem parS_double (s x : Nat) : parS (s + s) x = parS s (x ^^^ (x >>> s)) := by
  rw [parS_add, parS_xor]

theorem parS_of_lt {k x : Nat} (h : x < 2 ^ k) (n : Nat) : parS (k + n) x = parS k x := by
  rw [parS_add, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h, parS_zero_arg]
  exact Nat.xor_zero _

@[expose] noncomputable def parSt (s x : Nat) : Nat := Nat.xor x (Nat.shiftRight x s)

@[expose] noncomputable def parFold9 (x : Nat) : Nat :=
  Nat.land (parSt 1 (parSt 2 (parSt 4 (parSt 8 (parSt 16 (parSt 32 (parSt 64 (parSt 128
    (parSt 256 x))))))))) 1

theorem parS_one (x : Nat) : parS 1 x = Nat.land x 1 := by
  change Nat.xor 0 (Nat.land (Nat.shiftRight x 0) 1) = _
  simp only [Nat.xor_eq, Nat.zero_xor, Nat.shiftRight_eq', Nat.shiftRight_zero]

theorem parFold9_eq {x : Nat} (h : x < 2 ^ 300) : parFold9 x = parS 300 x := by
  have e : parS 300 x = parS (256 + 256) x := (parS_of_lt h 212).symm
  have st : ∀ s y, parS (s + s) y = parS s (parSt s y) := fun s y => parS_double s y
  rw [e]
  exact ((st 256 x).trans <| (st 128 _).trans <| (st 64 _).trans <| (st 32 _).trans <|
    (st 16 _).trans <| (st 8 _).trans <| (st 4 _).trans <| (st 2 _).trans <|
    (st 1 _).trans (parS_one _)).symm

@[expose] noncomputable def splitSolF : Bool :=
  splitRowsK.all fun r => Nat.beq (parFold9 (Nat.land r gamma0)) 0

theorem splitSolK_of_F (h : splitSolF = true) (hg : gamma0 < 2 ^ 300) : splitSolK = true := by
  rw [splitSolF, List.all_eq_true] at h
  rw [splitSolK, List.all_eq_true]
  intro r hr
  have hlt : Nat.land r gamma0 < 2 ^ 300 := lt_of_le_of_lt Nat.and_le_right hg
  rw [← parFold9_eq hlt, beq_iff_eq, ← Nat.beq_eq]
  exact h r hr

theorem beq_land_one (m i : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1 = m.testBit i := by
  rw [shiftRight_land_one]
  cases m.testBit i <;> rfl

theorem xorRowsFrom_eq : ∀ (rows : List Nat) (i m : Nat),
    xorRowsFrom i rows m = xorRowsS rows (Nat.shiftRight m i)
  | [], _, _ => rfl
  | r :: rs, i, m => by
    rw [xorRowsFrom, xorRowsFrom_eq rs (i + 1) m]
    change _ = Bool.rec (motive := fun _ => Nat) (xorRowsS rs (Nat.shiftRight (Nat.shiftRight m i) 1))
      (Nat.xor r (xorRowsS rs (Nat.shiftRight (Nat.shiftRight m i) 1)))
      (Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1)
    have e : Nat.shiftRight (Nat.shiftRight m i) 1 = Nat.shiftRight m (i + 1) := by
      simp only [Nat.shiftRight_eq', Nat.shiftRight_add]
    rw [e, beq_land_one]
    cases m.testBit i
    · simp
    · rfl

theorem splitMask_eq : splitMaskOK =
    (List.range 300).all fun u => xorRowsS splitRowsK (combSplit[u]!) == splitRes u := by
  simp only [splitMaskOK, xorRowsByMask, xorRowsFrom_eq, splitRows_eq, Nat.shiftRight_eq',
    Nat.shiftRight_zero]

theorem xorRowsS_zero : ∀ rows : List Nat, xorRowsS rows 0 = 0
  | [] => rfl
  | _ :: rows => xorRowsS_zero rows

theorem xorRowsS_take : ∀ (rows : List Nat) (n m : Nat), m < 2 ^ n →
    xorRowsS (rows.take n) m = xorRowsS rows m
  | [], _, _, _ => by simp
  | r :: rows, 0, m, h => by
    have hm : m = 0 := by omega
    subst hm
    rw [xorRowsS_zero, xorRowsS_zero]
  | r :: rows, n + 1, m, h => by
    have h' : Nat.shiftRight m 1 < 2 ^ n := by
      rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by omega)
    change Bool.rec (motive := fun _ => Nat) (xorRowsS (rows.take n) (Nat.shiftRight m 1))
        (Nat.xor r (xorRowsS (rows.take n) (Nat.shiftRight m 1))) (Nat.beq (Nat.land m 1) 1) =
      Bool.rec (motive := fun _ => Nat) (xorRowsS rows (Nat.shiftRight m 1))
        (Nat.xor r (xorRowsS rows (Nat.shiftRight m 1))) (Nat.beq (Nat.land m 1) 1)
    rw [xorRowsS_take rows n _ h']

@[expose] noncomputable def splitMaskP (rows : List Nat) (n lo : Nat) : Bool :=
  (List.range' lo 30).all fun u =>
    Nat.blt (combSplit[u]!) (Nat.pow 2 n) && xorRowsS rows (combSplit[u]!) == splitRes u

theorem splitMaskC_of_take (n lo : Nat) (h : splitMaskP (splitRowsK.take n) n lo = true) :
    splitMaskC lo = true := by
  rw [splitMaskC, List.all_eq_true]
  intro u hu
  have hu' := List.all_eq_true.1 h u hu
  rw [Bool.and_eq_true] at hu'
  have hlt : combSplit[u]! < 2 ^ n := by
    have h1 := hu'.1
    rw [Nat.blt_eq] at h1
    exact h1
  rw [← xorRowsS_take splitRowsK n _ hlt]
  exact hu'.2

theorem splitMask_of_chunks (h : ∀ j < 10, splitMaskC (30 * j) = true) : splitMaskOK = true := by
  rw [splitMask_eq]
  refine List.all_eq_true.2 fun u hu => ?_
  have hu' := List.mem_range.1 hu
  have hj := List.all_eq_true.1 (h (u / 30) (by omega)) u
    (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  exact hj

@[expose] noncomputable def dotG (x : Nat) : Nat := parS 300 (Nat.land x gamma0)

@[expose] noncomputable def dotF (x : Nat) : Nat := parFold9 (Nat.land x gamma0)

theorem dotF_eq (hg : gamma0 < 2 ^ 300) (x : Nat) : dotF x = dotG x :=
  parFold9_eq (lt_of_le_of_lt Nat.and_le_right hg)

theorem dotG_xor (x y : Nat) : dotG (x ^^^ y) = dotG x ^^^ dotG y := by
  rw [dotG, dotG, dotG, Nat.land_eq, Nat.land_eq, Nat.land_eq, Nat.and_xor_distrib_right,
    parS_xor]
  rfl

theorem dotG_zero : dotG 0 = 0 := by
  rw [dotG, Nat.land_eq, Nat.zero_and]
  exact parS_zero_arg 300

theorem getElem!_map_dotG (l : List Nat) (i : Nat) : (l.map dotG)[i]! = dotG l[i]! := by
  by_cases h : i < l.length
  · rw [getElem!_pos (l.map dotG) i (by simpa using h), getElem!_pos l i h, List.getElem_map]
  · rw [getElem!_neg (l.map dotG) i (by simpa using h), getElem!_neg l i h]
    exact dotG_zero.symm

theorem dotG_foldr {f F : Nat → Nat → Nat} (h : ∀ b acc, dotG (f b acc) = F b (dotG acc)) :
    ∀ l : List Nat, dotG (l.foldr f 0) = l.foldr F 0
  | [] => dotG_zero
  | b :: l => by rw [List.foldr_cons, List.foldr_cons, h, dotG_foldr h l]

theorem map_rowStepK (k : Nat) (first tail : List Nat) :
    (rowStepK k first tail).map dotG = rowStepK k (first.map dotG) (tail.map dotG) := by
  rw [rowStepK, rowStepK, List.map_map]
  congr 1
  funext rho
  rw [Function.comp_apply, dotG_xor, getElem!_map_dotG]
  congr 1
  refine dotG_foldr (fun rhop acc => ?_) ten
  split
  · rw [dotG_xor, getElem!_map_dotG]
  · rfl

@[expose] noncomputable def bitG (i x : Nat) : Nat := Nat.land (Nat.shiftRight x i) 1

theorem parS_two_pow_low (i : Nat) : ∀ m, m ≤ i → parS m (2 ^ i) = 0
  | 0, _ => rfl
  | m + 1, h => by
    change Nat.xor (parS m (2 ^ i)) (Nat.land (Nat.shiftRight (2 ^ i) m) 1) = 0
    rw [parS_two_pow_low i m (by omega), shiftRight_land_one, Nat.testBit_two_pow]
    split
    · next h' =>
      simp only [decide_eq_true_eq] at h'
      omega
    · rfl

theorem co2jc_testBit_false {x n i : Nat} (hx : x < 2 ^ n) (h : n ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right Nat.two_pos h))

theorem dotG_two_pow (hg : gamma0 < 2 ^ 300) (i : Nat) : dotG (2 ^ i) = bitG i gamma0 := by
  rw [dotG, bitG, shiftRight_land_one]
  by_cases h : gamma0.testBit i
  · simp only [h, ↓reduceIte]
    have hi : i < 300 := Nat.lt_of_not_le fun hc => by
      have hf := co2jc_testBit_false hg hc
      rw [hf] at h
      exact Bool.false_ne_true h
    have e : Nat.land (2 ^ i) gamma0 = 2 ^ i := by
      apply Nat.eq_of_testBit_eq
      intro m
      rw [Nat.land_eq, Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hm : i = m
      · subst hm
        simp [h]
      · simp [hm]
    have e1 : (2 ^ i) >>> i = 1 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_self (Nat.two_pow_pos i)]
    rw [e, (by omega : 300 = i + (1 + (299 - i))), parS_add, parS_two_pow_low i i le_rfl, e1,
      parS_of_lt (by decide : 1 < 2 ^ 1)]
    rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    have e : Nat.land (2 ^ i) gamma0 = 0 := by
      apply Nat.eq_of_testBit_eq
      intro m
      rw [Nat.land_eq, Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hm : i = m
      · subst hm
        simp [h]
      · simp [hm]
    rw [e]
    exact parS_zero_arg 300

@[expose] noncomputable def preMaskD (k rho v : Nat) : Nat :=
  ten.foldr
    (fun b acc => Bool.rec acc (bitG (100 * k + 10 * b + rho) gamma0 ^^^ acc)
      (Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1)) 0

@[expose] noncomputable def preMaskVecD (k v : Nat) : List Nat :=
  ten.map fun rho => preMaskD k rho v

@[expose] noncomputable def rowActD : List Nat → Nat → List Nat × Nat
  | [], j => (List.replicate 10 0, 2 ^ j)
  | k :: w, j => (rowStepK k (preMaskVecD k (rowActD w j).2) (rowActD w j).1, njK k (rowActD w j).2)

theorem preMaskVecD_eq (hg : gamma0 < 2 ^ 300) (k v : Nat) :
    preMaskVecD k v = (preMaskVecK k v).map dotG := by
  rw [preMaskVecD, preMaskVecK, List.map_map]
  congr 1
  funext rho
  rw [Function.comp_apply, preMaskD, preMaskK]
  refine (dotG_foldr (fun b acc => ?_) ten).symm
  cases Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1
  · rfl
  · change dotG (_ ^^^ acc) = bitG _ gamma0 ^^^ dotG acc
    rw [dotG_xor, dotG_two_pow hg]

theorem rowActD_eq (hg : gamma0 < 2 ^ 300) (j : Nat) :
    ∀ w, rowActD w j = ((rowActK w j).1.map dotG, (rowActK w j).2)
  | [] => by
    change (List.replicate 10 0, 2 ^ j) = ((List.replicate 10 0).map dotG, 2 ^ j)
    rw [List.map_replicate, dotG_zero]
  | k :: w => by
    rw [rowActD, rowActK, rowActD_eq hg j w, map_rowStepK, preMaskVecD_eq hg]

@[expose] noncomputable def splitSolD : Bool :=
  rels.all fun r => (List.range 10).all fun j => (rowActD r j).1.all fun x => Nat.beq x 0

theorem splitSolF_of_D (hg : gamma0 < 2 ^ 300) (h : splitSolD = true) : splitSolF = true := by
  have e (x : Nat) : parFold9 (Nat.land x gamma0) = dotG x := dotF_eq hg x
  rw [splitSolD] at h
  simp only [splitSolF, splitRowsK, List.all_flatMap, e]
  simp only [rowActD_eq hg, List.all_map, Function.comp_def] at h
  exact h

theorem bitG_xor (i x y : Nat) : bitG i (x ^^^ y) = bitG i x ^^^ bitG i y := by
  apply Nat.eq_of_testBit_eq
  intro m
  simp only [bitG, Nat.land_eq, Nat.shiftRight_eq', Nat.testBit_and, Nat.testBit_xor,
    Nat.testBit_shiftRight]
  cases (1 : Nat).testBit m <;> simp

theorem bitG_zero (i : Nat) : bitG i 0 = 0 := by
  rw [bitG, shiftRight_land_one, Nat.zero_testBit]
  rfl

theorem bitG_foldr (i : Nat) {f F : Nat → Nat → Nat}
    (h : ∀ b acc, bitG i (f b acc) = F b (bitG i acc)) :
    ∀ l : List Nat, bitG i (l.foldr f 0) = l.foldr F 0
  | [] => bitG_zero i
  | b :: l => by rw [List.foldr_cons, List.foldr_cons, h, bitG_foldr i h l]

@[expose] noncomputable def selG (f : Nat → Nat) (x : Nat) : Nat :=
  ten.foldr (fun b acc => Bool.rec acc (f b ^^^ acc)
    (Nat.beq (Nat.land (Nat.shiftRight x b) 1) 1)) 0

theorem bitG_selG (i : Nat) (f : Nat → Nat) (x : Nat) : bitG i (selG f x) =
    ten.foldr (fun b acc => Bool.rec acc (bitG i (f b) ^^^ acc)
      (Nat.beq (Nat.land (Nat.shiftRight x b) 1) 1)) 0 := by
  refine bitG_foldr i (fun b acc => ?_) ten
  cases Nat.beq (Nat.land (Nat.shiftRight x b) 1) 1
  · rfl
  · exact bitG_xor i _ _

@[expose] noncomputable def gRow (k b : Nat) : Nat :=
  Nat.land (Nat.shiftRight gamma0 (100 * k + 10 * b)) 1023

theorem bitG_gRow (k b rho : Nat) (h : rho < 10) :
    bitG rho (gRow k b) = bitG (100 * k + 10 * b + rho) gamma0 := by
  rw [bitG, bitG, shiftRight_land_one, shiftRight_land_one, gRow, Nat.land_eq, Nat.testBit_and,
    Nat.shiftRight_eq', Nat.testBit_shiftRight]
  have h1 : Nat.testBit 1023 rho = true := by
    have := Nat.testBit_two_pow_sub_one 10 rho
    simp only [h, decide_true] at this
    exact this
  rw [h1, Bool.and_true]

@[expose] noncomputable def dotWalk : List Nat → Nat → Nat × Nat
  | [], j => (0, 2 ^ j)
  | k :: w, j => (selG (gRow k) (dotWalk w j).2 ^^^ selG (fun r => njK k (2 ^ r)) (dotWalk w j).1,
      njK k (dotWalk w j).2)

@[expose] noncomputable def decodeG (t : Nat) : List Nat := ten.map fun rho => bitG rho t

theorem foldr_congr_mem {f g : Nat → Nat → Nat} :
    ∀ l : List Nat, (∀ a ∈ l, ∀ acc, f a acc = g a acc) → l.foldr f 0 = l.foldr g 0
  | [], _ => rfl
  | a :: l, h => by
    rw [List.foldr_cons, List.foldr_cons,
      foldr_congr_mem l fun b hb => h b (List.mem_cons_of_mem a hb),
      h a (List.mem_cons.2 (Or.inl rfl))]

theorem lt_of_mem_ten {a : Nat} (h : a ∈ ten) : a < 10 := by
  simp [ten] at h
  omega

theorem ten_map_get (f : Nat → Nat) {a : Nat} (h : a < 10) : (ten.map f)[a]! = f a := by
  have e : ten = List.range 10 := rfl
  have hl : a < ((List.range 10).map f).length := by simpa using h
  rw [e, getElem!_pos _ a hl, List.getElem_map, List.getElem_range]

theorem decodeG_step (k v t : Nat) :
    decodeG (selG (gRow k) v ^^^ selG (fun r => njK k (2 ^ r)) t) =
      rowStepK k (preMaskVecD k v) (decodeG t) := by
  rw [decodeG, rowStepK]
  apply List.map_congr_left
  intro rho hrho
  have hr := lt_of_mem_ten hrho
  rw [bitG_xor, preMaskVecD, ten_map_get _ hr]
  congr 1
  · rw [bitG_selG, preMaskD]
    refine foldr_congr_mem ten fun b _ acc => ?_
    rw [bitG_gRow k b rho hr]
  · rw [bitG_selG]
    refine foldr_congr_mem ten fun rhop hp acc => ?_
    rw [decodeG, ten_map_get _ (lt_of_mem_ten hp), beq_land_one, bitG, bitG, shiftRight_land_one,
      shiftRight_land_one]
    cases t.testBit rhop <;> cases (njK k (2 ^ rhop)).testBit rho <;> simp

theorem rowActD_walk (j : Nat) : ∀ w, rowActD w j = (decodeG (dotWalk w j).1, (dotWalk w j).2)
  | [] => by
    change (List.replicate 10 0, 2 ^ j) = (decodeG 0, 2 ^ j)
    simp only [decodeG, bitG_zero]
    rfl
  | k :: w => by rw [rowActD, dotWalk, rowActD_walk j w, decodeG_step]

@[expose] noncomputable def splitSolW : Bool :=
  rels.all fun r => (List.range 10).all fun j => Nat.beq (dotWalk r j).1 0

theorem splitSolD_of_W (h : splitSolW = true) : splitSolD = true := by
  rw [splitSolW, List.all_eq_true] at h
  rw [splitSolD, List.all_eq_true]
  intro r hr
  have h1 := List.all_eq_true.1 (h r hr)
  refine List.all_eq_true.2 fun j hj => ?_
  have h2 : (dotWalk r j).1 = 0 := Nat.eq_of_beq_eq_true (h1 j hj)
  rw [rowActD_walk, h2]
  rfl

@[expose] noncomputable def splitSolWR (lo n : Nat) : Bool :=
  (List.range' lo n).all fun i => (List.range 10).all fun j => Nat.beq (dotWalk rels[i]! j).1 0

theorem splitSolW_of_chunks (h : ∀ c < 5, splitSolWR (5 * c) 5 = true) : splitSolW = true := by
  have hl : rels.length = 25 := rfl
  rw [splitSolW, List.all_eq_true]
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < 25 := hl ▸ hi
  have := List.all_eq_true.1 (h (i / 5) (by omega)) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  rwa [getElem!_pos rels i hi] at this

theorem rowActK_len (j : Nat) : ∀ w, (rowActK w j).1.length = 10
  | [] => rfl
  | _ :: _ => by rw [rowActK, rowStepK, List.length_map]; rfl

theorem relRows_len (r : List Nat) : (relRows r).length = 100 := by
  rw [relRows, List.length_flatMap]
  simp only [rowActK_len]
  rfl

theorem flatMap_relRows_len (l : List (List Nat)) :
    (l.flatMap relRows).length = 100 * l.length := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [List.flatMap_cons, List.length_append, ih, relRows_len, List.length_cons]
    omega

theorem splitRowsK_len : splitRowsK.length = 2500 := by
  have e : splitRowsK = rels.flatMap relRows := rfl
  rw [e, flatMap_relRows_len]
  rfl

theorem splitRowsK_take400 : splitRowsK.take 400 =
    relRows rels[0]! ++ relRows rels[1]! ++ relRows rels[2]! ++ relRows rels[3]! := by
  have e : splitRowsK = (rels.take 4).flatMap relRows ++ (rels.drop 4).flatMap relRows := by
    rw [← List.flatMap_append, List.take_append_drop]
    rfl
  have e4 : rels.take 4 = [rels[0]!, rels[1]!, rels[2]!, rels[3]!] := rfl
  rw [e, List.take_left' (by rw [flatMap_relRows_len]; rfl), e4]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

end CertificateChecks.KernelCo2Jc
