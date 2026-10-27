module
public import CFSG.Sporadic.HNSchreier.HexDecode
public import Lean.CoreM

public section
set_option maxHeartbeats 1000000
namespace CFSG.Sporadic.HNSchreier.Native.Kernel

theorem byteArray_forIn_eq {β : Type} (bs : ByteArray) (b : β)
    (f : UInt8 → β → Id (ForInStep β)) :
    forIn bs b f = forIn bs.data b f := by
  change ByteArray.forIn bs b f = Array.forIn' bs.data b (fun a _ st => f a st)
  have aux (i : Nat) (h : i ≤ bs.size) (st : β) :
      ByteArray.forIn.loop bs f i h st =
        Array.forIn'.loop bs.data (fun a _ st => f a st) i h st := by
    induction i generalizing st with
    | zero => rfl
    | succ i ih =>
      have hs : bs.data.size = bs.size := rfl
      change (match f bs[bs.size - 1 - i] st with
        | .done t => t
        | .yield t => ByteArray.forIn.loop bs f i (by omega) t) =
        (match f bs[bs.size - 1 - i] st with
        | .done t => t
        | .yield t => Array.forIn'.loop bs.data (fun a _ st => f a st) i (by omega) t)
      split
      · rfl
      · exact ih _ _
  exact aux bs.size (Nat.le_refl _) b

abbrev State := List UInt8 × Bool × Nat × Bool

@[expose] def step (st : State) (c : UInt8) : State :=
  let (out, body, hi, half) := st
  if !body then
    if c == 10 then (out, true, hi, half) else st
  else if isHexDigitB c then
    if half then (UInt8.ofNat (16 * hi + hexValB c) :: out, body, hi, false)
    else (out, body, hexValB c, true)
  else st

@[expose] def hexDumpBytesFast (s : String) : ByteArray :=
  ⟨⟨((s.toUTF8.data.toList.foldl step ([], false, 0, false)).1).reverse⟩⟩

abbrev ByteState := ByteArray × Bool × Nat × Bool

def pack (st : State) : ByteState :=
  (⟨⟨st.1.reverse⟩⟩, st.2)

def slowStep (st : ByteState) (c : UInt8) : ByteState :=
  let (out, body, hi, half) := st
  if !body then
    if c == 10 then (out, true, hi, half) else st
  else if isHexDigitB c then
    if half then (out.push (UInt8.ofNat (16 * hi + hexValB c)), body, hi, false)
    else (out, body, hexValB c, true)
  else st

theorem step_pack (st : State) (c : UInt8) : slowStep (pack st) c = pack (step st c) := by
  rcases st with ⟨out, body, hi, half⟩
  cases body <;> cases half <;> by_cases h : c == 10 <;>
    by_cases hh : isHexDigitB c <;>
    simp_all [step, slowStep, pack, ByteArray.push, Array.push, List.reverse_cons]

theorem fold_pack (xs : List UInt8) (st : State) :
    xs.foldl slowStep (pack st) = pack (xs.foldl step st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons c xs ih => simpa only [List.foldl_cons, step_pack] using ih (step st c)

theorem pure_ite_yield (p : Prop) [Decidable p] (a b : ByteState) :
    (if p then (pure (.yield a) : Id (ForInStep ByteState)) else pure (.yield b)) =
      pure (.yield (if p then a else b)) := by split <;> rfl

theorem hexDumpBytes_eq_fast (s : String) : hexDumpBytes s = hexDumpBytesFast s := by
  unfold hexDumpBytes
  simp only [byteArray_forIn_eq]
  simp only [pure_ite_yield]
  change ((forIn s.toUTF8.data (pack ([], false, 0, false))
    (fun c st => pure (.yield (slowStep st c)))) : Id ByteState).run.fst = hexDumpBytesFast s
  rw [Array.forIn_pure_yield_eq_foldl]
  change (s.toUTF8.data.foldl slowStep (pack ([], false, 0, false))).1 = _
  rw [← Array.foldl_toList, fold_pack]
  rfl

@[expose] def hexDumpChars (cs : List Char) : ByteArray :=
  ⟨⟨((cs.foldl (fun st c => (String.utf8EncodeChar c).foldl step st)
    ([], false, 0, false)).1).reverse⟩⟩

theorem hexDumpBytes_ofList (cs : List Char) :
    hexDumpBytes (String.ofList cs) = hexDumpChars cs := by
  rw [hexDumpBytes_eq_fast]
  simp only [hexDumpBytesFast, hexDumpChars, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList, List.utf8Encode, List.data_toByteArray,
    List.toList_toArray, List.foldl_flatMap]

@[expose] def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 87 + n)

@[expose] def hexChars (b : UInt8) : List Char :=
  [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

@[expose] def encodeBytes (bs : List UInt8) : String :=
  String.ofList ('\n' :: bs.flatMap hexChars)

private theorem digit_facts : ∀ n : Fin 256,
    let hi := UInt8.ofNat (hexDigit (n.val / 16)).toNat
    let lo := UInt8.ofNat (hexDigit (n.val % 16)).toNat
    String.utf8EncodeChar (hexDigit (n.val / 16)) = [hi] ∧
    String.utf8EncodeChar (hexDigit (n.val % 16)) = [lo] ∧
    isHexDigitB hi = true ∧ isHexDigitB lo = true ∧
    UInt8.ofNat (16 * hexValB hi + hexValB lo) = UInt8.ofNat n.val := by
  decide +kernel

theorem hexChars_step (b : UInt8) (out : List UInt8) (hi : Nat) :
    (hexChars b).foldl (fun st c => (String.utf8EncodeChar c).foldl step st)
      (out, true, hi, false) =
      (b :: out, true, hexValB (UInt8.ofNat (hexDigit (b.toNat / 16)).toNat), false) := by
  have hf := digit_facts ⟨b.toNat, b.toNat_lt_size⟩
  dsimp only at hf
  rcases hf with ⟨h1, h2, h3, h4, h5⟩
  simp only [hexChars, List.foldl_cons, List.foldl_nil, h1, h2, step,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, h3, h4,
    UInt8.ofNat_toNat, h5]

theorem encodeBytes_decode (bs : List UInt8) : hexDumpBytes (encodeBytes bs) = ⟨⟨bs⟩⟩ := by
  rw [encodeBytes, hexDumpBytes_ofList]
  have aux (xs : List UInt8) (out : List UInt8) (hi : Nat) :
      ((xs.flatMap hexChars).foldl (fun st c => (String.utf8EncodeChar c).foldl step st)
        (out, true, hi, false)).1 = xs.reverse ++ out := by
    induction xs generalizing out hi with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.foldl_append, hexChars_step, ih,
        List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
  simp only [hexDumpChars, List.foldl_cons]
  change (⟨⟨(((bs.flatMap hexChars).foldl
    (fun st c => (String.utf8EncodeChar c).foldl step st)
    ([], true, 0, false)).1).reverse⟩⟩ : ByteArray) = _
  rw [aux]
  simp

end CFSG.Sporadic.HNSchreier.Native.Kernel
