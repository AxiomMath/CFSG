module

public import Certificates.Data.Kernel.B45Ind.M23
public import Certificates.Data.Kernel.B45Ind.M24

public section

namespace CFSG.KC.B45Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.B45Mat.Ind

@[expose] def tbK (x i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight x i) 1) 1

theorem testBit_eq_tbK (x i : ℕ) : x.testBit i = tbK x i := by
  have h : Nat.land (Nat.shiftRight x i) 1 = x / 2 ^ i % 2 := by
    show (x >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold tbK
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h2 | h2 <;> rw [h2] <;> rfl

@[expose] def forceN {α : Type} (y : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

theorem forceN_eq {α : Type} : ∀ (y : ℕ) (k : ℕ → α), forceN y k = k y
  | 0, _ => rfl
  | _ + 1, _ => rfl

@[expose] def papK (d : ℕ) : List ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ r cs v acc => r cs.tail (Nat.shiftRight v 1)
      (cond (Nat.beq (Nat.land v 1) 1) (Nat.xor acc (cs.headD 0)) acc)) d

theorem headD_drop_getD' : ∀ (l : List ℕ) (j : ℕ), (l.drop j).headD 0 = l.getD j 0
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | _ :: l, j + 1 => by
    rw [List.drop_succ_cons, headD_drop_getD' l j]
    simp

theorem foldl_eq_papK (L : List ℕ) (V : ℕ) : ∀ (d j acc : ℕ),
    (List.range' j d).foldl (fun acc i => if V.testBit i then acc ^^^ L.getD i 0 else acc) acc =
      papK d (L.drop j) (V >>> j) acc
  | 0, _, _ => rfl
  | d + 1, j, acc => by
    have e : papK (d + 1) (L.drop j) (V >>> j) acc = papK d (L.drop j).tail
        (Nat.shiftRight (V >>> j) 1)
        (cond (Nat.beq (Nat.land (V >>> j) 1) 1) (Nat.xor acc ((L.drop j).headD 0)) acc) := rfl
    have hs : Nat.shiftRight (V >>> j) 1 = V >>> (j + 1) := (Nat.shiftRight_add V j 1).symm
    have hb : (if V.testBit j then acc ^^^ L.getD j 0 else acc) =
        cond (Nat.beq (Nat.land (V >>> j) 1) 1) (Nat.xor acc ((L.drop j).headD 0)) acc := by
      rw [headD_drop_getD', show Nat.beq (Nat.land (V >>> j) 1) 1 = tbK V j from rfl,
        ← testBit_eq_tbK]
      cases V.testBit j <;> rfl
    simp only [List.range'_succ, List.foldl_cons]
    rw [foldl_eq_papK L V d (j + 1), e, hs, hb, List.tail_drop]

theorem papply_eq_papK (d : ℕ) (cols : List ℕ) (v : ℕ) : papply d cols v = papK d cols v 0 := by
  unfold papply
  rw [List.range_eq_range', foldl_eq_papK cols v d 0 0, List.drop_zero, Nat.shiftRight_zero]

@[expose] def baseOKK (N : ℕ) (P Pi : List ℕ) : Bool :=
  (List.range N).all (fun j => papK N Pi (P.getD j 0) 0 == 1 <<< j) &&
    (List.range N).all fun j => papK N P (Pi.getD j 0) 0 == 1 <<< j

@[expose] def conjColsK (N : ℕ) (Pi K P : List ℕ) : List ℕ :=
  (List.range N).map fun j => papK N Pi (papK N K (P.getD j 0) 0) 0

@[expose] def flagCoreK (N : ℕ) (K : Bool → List ℕ) (P Pi : List ℕ) (ns : List ℕ)
    (blk : ℕ → Bool → List ℕ) : Bool :=
  baseOKK N P Pi && nsOK N ns &&
    flagSide ns (fun i => blk i false) (conjColsK N Pi (K false) P) &&
    flagSide ns (fun i => blk i true) (conjColsK N Pi (K true) P)

theorem flagCore_eq_flagCoreK (N : ℕ) (K : Bool → List ℕ) (P Pi : List ℕ) (ns : List ℕ)
    (blk : ℕ → Bool → List ℕ) : flagCore N K P Pi ns blk = flagCoreK N K P Pi ns blk := by
  simp only [flagCore, flagCoreK, baseOK, baseOKK, conjCols, conjColsK, papply_eq_papK]

theorem flagCoreK_of {N : ℕ} {K : Bool → List ℕ} {P Pi ns : List ℕ} {blk : ℕ → Bool → List ℕ}
    (h1 : (baseOKK N P Pi && nsOK N ns) = true)
    (h2 : flagSide ns (fun i => blk i false) (conjColsK N Pi (K false) P) = true)
    (h3 : flagSide ns (fun i => blk i true) (conjColsK N Pi (K true) P) = true) :
    flagCoreK N K P Pi ns blk = true := by
  rw [flagCoreK, h1, h2, h3]
  try rfl

@[expose] def scanK (i : ℕ) (l : List (ℕ × ℕ)) : ℕ → Option ℕ :=
  List.rec (motive := fun _ => ℕ → Option ℕ) (fun _ => none)
    (fun e _ r k => cond (Nat.ble i k && tbK e.1 i) (some k) (r (Nat.succ k))) l

@[expose] def elimK (i p1 p2 : ℕ) (l : List (ℕ × ℕ)) : ℕ → List (ℕ × ℕ) :=
  List.rec (motive := fun _ => ℕ → List (ℕ × ℕ)) (fun _ => [])
    (fun e _ r k => cond (!Nat.beq k i && tbK e.1 i)
      (forceN (Nat.xor e.1 p1) fun a => forceN (Nat.xor e.2 p2) fun b => (a, b) :: r (Nat.succ k))
      (e :: r (Nat.succ k))) l

@[expose] def elimSw (i : ℕ) (st : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  elimK i (st.getD i (0, 0)).1 (st.getD i (0, 0)).2 st 0

@[expose] def invStepK (st : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) :=
  Option.rec (motive := fun _ => List (ℕ × ℕ)) st (fun j => elimSw i (swapL st i j)) (scanK i st 0)

@[expose] def invColsK (n : ℕ) (P : List ℕ) : List ℕ :=
  ((List.range n).foldl invStepK ((List.range n).map fun j => (P.getD j 0, 1 <<< j))).map (·.2)

theorem decide_le_eq_ble (i k : ℕ) : decide (i ≤ k) = Nat.ble i k := by
  cases h : Nat.ble i k
  · have : ¬ i ≤ k := Nat.not_le_of_not_ble_eq_true (by simp [h])
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

theorem bne_eq_not_beq (k i : ℕ) : (k != i) = !Nat.beq k i := by
  cases h : Nat.beq k i
  · have : k ≠ i := Nat.ne_of_beq_eq_false h
    simp [this]
  · have : k = i := Nat.eq_of_beq_eq_true h
    subst this
    simp

theorem scanIdx_eq_scanK (i : ℕ) : ∀ (l : List (ℕ × ℕ)) (k : ℕ),
    scanIdx (fun e : ℕ × ℕ => e.1.testBit i) i k l = scanK i l k
  | [], _ => rfl
  | e :: l, k => by
    show (if (decide (i ≤ k) && e.1.testBit i) = true then some k
        else scanIdx (fun e : ℕ × ℕ => e.1.testBit i) i (k + 1) l) =
      cond (Nat.ble i k && tbK e.1 i) (some k) (scanK i l (Nat.succ k))
    rw [scanIdx_eq_scanK i l (k + 1), testBit_eq_tbK, decide_le_eq_ble]
    cases (Nat.ble i k && tbK e.1 i) <;> rfl

theorem mapIdxFrom_eq_elimK (i : ℕ) (p : ℕ × ℕ) : ∀ (l : List (ℕ × ℕ)) (k : ℕ),
    mapIdxFrom (fun j' (e : ℕ × ℕ) =>
        if (j' != i && e.1.testBit i) = true then (e.1 ^^^ p.1, e.2 ^^^ p.2) else e) k l =
      elimK i p.1 p.2 l k
  | [], _ => rfl
  | e :: l, k => by
    show (if (k != i && e.1.testBit i) = true then (e.1 ^^^ p.1, e.2 ^^^ p.2) else e) ::
        mapIdxFrom (fun j' (e : ℕ × ℕ) =>
          if (j' != i && e.1.testBit i) = true then (e.1 ^^^ p.1, e.2 ^^^ p.2) else e) (k + 1) l =
      cond (!Nat.beq k i && tbK e.1 i)
        (forceN (Nat.xor e.1 p.1) fun a => forceN (Nat.xor e.2 p.2) fun b =>
          (a, b) :: elimK i p.1 p.2 l (Nat.succ k))
        (e :: elimK i p.1 p.2 l (Nat.succ k))
    simp only [forceN_eq]
    rw [mapIdxFrom_eq_elimK i p l (k + 1), testBit_eq_tbK, bne_eq_not_beq]
    cases (!Nat.beq k i && tbK e.1 i) <;> rfl

theorem invStepL_eq_invStepK (st : List (ℕ × ℕ)) (i : ℕ) : invStepL st i = invStepK st i := by
  unfold invStepL invStepK pivL
  rw [scanIdx_eq_scanK]
  cases scanK i st 0 with
  | none => rfl
  | some j =>
    exact mapIdxFrom_eq_elimK i ((swapL st i j).getD i (0, 0)) (swapL st i j) 0

theorem invColsL_eq_invColsK (n : ℕ) (P : List ℕ) : invColsL n P = invColsK n P := by
  have h : invStepL = invStepK := funext fun st => funext fun i => invStepL_eq_invStepK st i
  unfold invColsL invColsK
  rw [h]

theorem flag23L_eq_K (i : ℕ) : flag23L i =
    flagCoreK (23 * m23Xd i) (k23L i) (m23P i) (invColsK (23 * m23Xd i) (m23P i)) (m23Ns i)
      (fun j => m23Std ((m23Typs i).getD j 0)) := by
  rw [flag23L, flagCore_eq_flagCoreK, invColsL_eq_invColsK]

theorem flag24L_eq_K (i : ℕ) : flag24L i =
    flagCoreK (24 * m24Xd i) (k24L i) (m24P i) (invColsK (24 * m24Xd i) (m24P i)) (m24Ns i)
      (fun j => m24Std ((m24Typs i).getD j 0)) := by
  rw [flag24L, flagCore_eq_flagCoreK, invColsL_eq_invColsK]

end CFSG.KC.B45Ind

end
