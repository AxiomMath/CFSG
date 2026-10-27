module

public section

namespace CFSG.Monster.B.Dyadic.Native

@[expose] def dim (_ : Unit := ()) : Nat := 4371

@[expose, irreducible] def latticeText : String := include_str "../../../../CFSG/Monster/B/Data/lattice4371.txt"

@[inline, expose] def b64val (c : UInt8) : Nat :=
  let c := c.toNat
  if 65 ≤ c ∧ c ≤ 90 then c - 65
  else if 97 ≤ c ∧ c ≤ 122 then c - 71
  else if 48 ≤ c ∧ c ≤ 57 then c + 4
  else if c = 43 then 62
  else if c = 47 then 63
  else 0

@[expose] def b64decode (s : ByteArray) (start stop : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity ((stop - start) / 4 * 3)
  let mut i := start
  while i + 4 ≤ stop do
    let x := (b64val (s.get! i) <<< 18) ||| (b64val (s.get! (i + 1)) <<< 12) |||
      (b64val (s.get! (i + 2)) <<< 6) ||| b64val (s.get! (i + 3))
    out := ((out.push (UInt8.ofNat (x >>> 16))).push (UInt8.ofNat (x >>> 8))).push (UInt8.ofNat x)
    i := i + 4
  return out

@[expose, irreducible] def lineBreak (_ : Unit := ()) : Nat := Id.run do
  let b := latticeText.toUTF8
  let mut k := 0
  while k < b.size && b.get! k != 10 do
    k := k + 1
  return k

@[expose, irreducible] def diagExp (_ : Unit := ()) : Array Nat :=
  let b := latticeText.toUTF8
  Array.ofFn (n := dim) fun i => (b.get! i.val).toNat - 48

@[expose, irreducible] def upperBits (_ : Unit := ()) : ByteArray :=
  let b := latticeText.toUTF8
  let stop := Id.run do
    let mut k := lineBreak + 1
    while k < b.size && b.get! k != 10 do
      k := k + 1
    return k
  b64decode b (lineBreak + 1) stop

@[expose, irreducible] def basisRows (_ : Unit := ()) : Array ByteArray := Id.run do
  let n := dim
  let bits := upperBits
  let mut rows : Array ByteArray := Array.mkEmpty n
  let mut acc : Nat := 0
  let mut nb : Nat := 0
  let mut pos : Nat := 0
  for i in [0:n] do
    let mut row := ByteArray.mk (Array.replicate n 0)
    row := row.set! i (UInt8.ofNat (1 <<< diagExp[i]!))
    for j in [i + 1:n] do
      while nb < 7 do
        acc := acc ||| ((bits.get! pos).toNat <<< nb)
        pos := pos + 1
        nb := nb + 8
      row := row.set! j (UInt8.ofNat (acc &&& 127))
      acc := acc >>> 7
      nb := nb - 7
    rows := rows.push row
  return rows

end CFSG.Monster.B.Dyadic.Native
