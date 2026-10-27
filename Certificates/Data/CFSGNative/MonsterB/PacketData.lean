module

public section

namespace CFSG.Monster.B.Native

@[inline, expose] def b64Val (c : UInt8) : Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then n - 65
  else if 97 ≤ n ∧ n ≤ 122 then n - 71
  else if 48 ≤ n ∧ n ≤ 57 then n + 4
  else if n = 43 then 62
  else if n = 47 then 63
  else 64

@[inline, expose] def numOfCode (c : Nat) : Int :=
  match c with
  | 0 => 8
  | 1 => -8
  | 2 => 4
  | 3 => -4
  | 4 => 2
  | 5 => -2
  | _ => 0

@[expose] def decodeRows (s : String) : Array (Array (Array (Nat × Int))) := Id.run do
  let b := s.toUTF8
  let mut gens : Array (Array (Array (Nat × Int))) := #[]
  let mut rows : Array (Array (Nat × Int)) := #[]
  let mut row : Array (Nat × Int) := #[]
  let mut acc : Nat := 0
  let mut cnt : Nat := 0
  for i in [0:b.size] do
    let c := b.get! i
    if c == 10 then
      gens := gens.push rows
      rows := #[]
    else
      acc := acc * 64 + b64Val c
      cnt := cnt + 1
      if cnt == 3 then
        row := row.push (acc % 8192, numOfCode (acc / 8192 % 8))
        if acc / 65536 == 1 then
          rows := rows.push row
          row := #[]
        acc := 0
        cnt := 0
  return gens

@[inline, expose] def hexDigit (c : UInt8) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else c.toNat - 55

@[expose] def hexNum (b : ByteArray) (o : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => hexNum b o w * 16 + hexDigit (b.get! (o + w))

@[expose] def packetRowsText : String :=
  include_str "../../../../CFSG/Monster/B/Data/packet4371-rows.txt"

@[expose] def packetLabelsText : String :=
  include_str "../../../../CFSG/Monster/B/Data/packet4371-labels.txt"

@[expose] def packetRows (_ : Unit := ()) : Array (Array (Array (Nat × Int))) := decodeRows packetRowsText

@[expose] def pauliAt (b : ByteArray) (o : Nat) : Nat × Nat × Nat :=
  (hexNum b o 1, hexNum b (o + 1) 3, hexNum b (o + 4) 3)

@[expose] def packetLabels (_ : Unit := ()) : Array ((Nat × Nat × Nat) × (Nat × Nat × Nat)) :=
  let b := packetLabelsText.toUTF8
  Array.ofFn (n := 2300) fun i => (pauliAt b (14 * i.val), pauliAt b (14 * i.val + 7))

@[expose] def packetSpinIndices (_ : Unit := ()) : Array Nat :=
  let b := packetLabelsText.toUTF8
  Array.ofFn (n := 2048) fun i => hexNum b (2300 * 14 + 1 + 3 * i.val) 3

@[expose] def packetRowShapeOK (row : Array (Nat × Int)) : Bool :=
  row.size ≥ 1 && (List.range row.size).all fun t =>
    (row[t]!).1 < 4371 && (t == 0 || (row[t - 1]!).1 < (row[t]!).1)

@[expose] def packetShapeOK (_ : Unit := ()) : Bool :=
  packetRows.size == 48 && packetRows.all fun g => g.size == 4371 && g.all packetRowShapeOK

@[expose] def packetEntryCount (_ : Unit := ()) : Nat :=
  packetRows.foldl (fun n g => g.foldl (fun n r => n + r.size) n) 0

end CFSG.Monster.B.Native
