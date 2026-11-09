module

public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

namespace CertificateChecks.KernelCo2SmithS

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Smith.Native

@[expose] def vecK (d : Nat) : List Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => List Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ r cs v acc => r cs.tail (Nat.shiftRight v 1)
      (cond (Nat.beq (Nat.land v 1) 1) (Nat.xor acc (cs.headD 0)) acc)) d

theorem testBit_eq_beq' (x i : Nat) : x.testBit i = Nat.beq (Nat.land (x >>> i) 1) 1 := by
  have h : Nat.land (x >>> i) 1 = x / 2 ^ i % 2 := by
    show (x >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h2 | h2 <;> rw [h2] <;> rfl

theorem headD_drop_getD'' : ∀ (l : List Nat) (j : Nat), (l.drop j).headD 0 = l.getD j 0
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | _ :: l, j + 1 => by
    rw [List.drop_succ_cons, headD_drop_getD'' l j]
    simp

theorem foldl_eq_vecK (L : List Nat) (V : Nat) : ∀ (d j acc : Nat),
    (List.range' j d).foldl (fun acc i => if V.testBit i then acc ^^^ L.getD i 0 else acc) acc =
      vecK d (L.drop j) (V >>> j) acc
  | 0, _, _ => rfl
  | d + 1, j, acc => by
    have e : vecK (d + 1) (L.drop j) (V >>> j) acc = vecK d (L.drop j).tail
        (Nat.shiftRight (V >>> j) 1)
        (cond (Nat.beq (Nat.land (V >>> j) 1) 1) (Nat.xor acc ((L.drop j).headD 0)) acc) := rfl
    have hs : Nat.shiftRight (V >>> j) 1 = V >>> (j + 1) := (Nat.shiftRight_add V j 1).symm
    have hb : (if V.testBit j then acc ^^^ L.getD j 0 else acc) =
        cond (Nat.beq (Nat.land (V >>> j) 1) 1) (Nat.xor acc ((L.drop j).headD 0)) acc := by
      rw [headD_drop_getD'', ← testBit_eq_beq']
      cases V.testBit j <;> rfl
    simp only [List.range'_succ, List.foldl_cons]
    rw [foldl_eq_vecK L V d (j + 1), e, hs, hb, List.tail_drop]

theorem vecMulN_eq_vecK (d : Nat) (R : Array Nat) (v : Nat) : vecMulN d R v = vecK d R.toList v 0 := by
  have hR : (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) =
      (fun acc j => if v.testBit j then acc ^^^ R.toList.getD j 0 else acc) := by
    funext acc j
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  unfold vecMulN
  rw [hR, List.range_eq_range', foldl_eq_vecK R.toList v d 0 0, List.drop_zero, Nat.shiftRight_zero]

@[expose] def mulRowsK (d : Nat) (X Y : Array Nat) : Array Nat := X.map fun v => vecK d Y.toList v 0

theorem mulRows_eq_mulRowsK (d : Nat) (X Y : Array Nat) : mulRows d X Y = mulRowsK d X Y := by
  unfold mulRows mulRowsK
  congr 1
  funext v
  exact vecMulN_eq_vecK d Y v

@[expose] def powRowsK (d : Nat) (M : Array Nat) : Nat → Array Nat
  | 0 => idRows d
  | e + 1 => mulRowsK d (powRowsK d M e) M

theorem powRows_eq_powRowsK (d : Nat) (M : Array Nat) : ∀ e, powRows d M e = powRowsK d M e
  | 0 => rfl
  | e + 1 => by
    rw [powRows, powRowsK, powRows_eq_powRowsK d M e, mulRows_eq_mulRowsK]

@[expose] def wRowsK (L : Array (Array Nat)) : List Nat → Array Nat
  | [] => idRows 22
  | k :: w => mulRowsK 22 L[k]! (wRowsK L w)

theorem wRows_eq_wRowsK (L : Array (Array Nat)) : ∀ w, wRows L w = wRowsK L w
  | [] => rfl
  | k :: w => by
    rw [wRows, wRowsK, wRows_eq_wRowsK L w, mulRows_eq_mulRowsK]

@[expose] def lettersK (seeds : Array (Array Nat)) : Array (Array Nat) :=
  #[seeds[0]!, seeds[1]!, wRowsK seeds aWord, wRowsK seeds bWord]

@[expose] def mRowsK (seeds : Array (Array Nat)) (w : List Nat) : Array Nat :=
  wRowsK (lettersK seeds) w

@[expose] def fRowsK (seeds : Array (Array Nat)) : Array (Array Nat) :=
  frameWords.map (mRowsK seeds)

theorem mRows_eq_mRowsK (seeds : Array (Array Nat)) (w : List Nat) :
    mRows seeds w = mRowsK seeds w := by
  simp only [mRows, mRowsK, letters, lettersK, wRows_eq_wRowsK]

theorem fRows_eq_fRowsK (seeds : Array (Array Nat)) : fRows seeds = fRowsK seeds := by
  unfold fRows fRowsK
  congr 1
  funext w
  exact mRows_eq_mRowsK seeds w

@[expose] def frameOKK (seeds : Array (Array Nat)) : Bool :=
  let F := fRowsK seeds
  let I := idRows 22
  let sw := fun (i : Nat) => if i == 0 then 1 else if i == 1 then 0 else i
  let sw' := fun (i : Nat) => if i == 1 then 2 else if i == 2 then 1 else i
  F.size == 10 &&
  (List.range 3).all (fun i =>
    let y := F[2 * i]!
    let s := F[2 * i + 1]!
    powRowsK 22 y 3 == I && mulRowsK 22 s s == I &&
      mulRowsK 22 (mulRowsK 22 s y) s == mulRowsK 22 y y) &&
  (List.range 3).all (fun i => (List.range 3).all fun j => i == j ||
    (List.range 2).all fun e => (List.range 2).all fun e' =>
      mulRowsK 22 F[2 * i + e]! F[2 * j + e']! == mulRowsK 22 F[2 * j + e']! F[2 * i + e]!) &&
  (List.range 6).all (fun k =>
    mulRowsK 22 F[6]! F[k]! == mulRowsK 22 F[2 * sw (k / 2) + k % 2]! F[6]! &&
      mulRowsK 22 F[7]! F[k]! == mulRowsK 22 F[2 * sw' (k / 2) + k % 2]! F[7]!) &&
  powRowsK 22 F[8]! 5 == I && mulRowsK 22 F[8]! F[0]! == mulRowsK 22 F[0]! F[8]! &&
  mulRowsK 22 F[8]! F[1]! == mulRowsK 22 F[1]! F[8]! &&
  mulRowsK 22 F[9]! F[8]! == mulRowsK 22 (mulRowsK 22 F[8]! F[8]!) F[9]! &&
  mulRowsK 22 F[9]! F[0]! == mulRowsK 22 F[0]! F[9]! &&
  pinRels.all (fun r => powRowsK 22 (mulRowsK 22 F[8]! (wRowsK F r.1)) r.2 == I) &&
  wRowsK F genAWord == mRowsK seeds [2] && wRowsK F genBWord == mRowsK seeds [3]

theorem frameOK_eq_frameOKK (seeds : Array (Array Nat)) : frameOK seeds = frameOKK seeds := by
  simp only [frameOK, frameOKK, fRows_eq_fRowsK, conjTo, commRows, mulRows_eq_mulRowsK,
    powRows_eq_powRowsK, wRows_eq_wRowsK, mRows_eq_mRowsK]

end CertificateChecks.KernelCo2SmithS

end
