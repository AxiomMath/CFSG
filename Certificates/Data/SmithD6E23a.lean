module

public import Certificates.Data.SmithD6Model

public noncomputable section

namespace CFSG.SmithD6

@[expose] def ea7Bits : List Nat := [2, 3, 4, 5, 8, 9, 14, 15, 16, 17, 22, 23, 26, 27, 28, 29]

@[expose] def ea7Diff (k m : Nat) : Nat := (tvCols k)[m]! ^^^ 2 ^ m

@[expose] def ea7Pivot (k : Nat) : Bool :=
  (List.range 32).all fun m₀ => ea7Diff k m₀ == 0 ||
    (List.range 32).any fun j => (ea7Diff k m₀).testBit j &&
      (List.range 32).all fun m => m == m₀ || !(ea7Diff k m).testBit j

@[expose] def ea7ChkCols : Bool := ea7Pivot 0 && ea7Pivot 31899

@[expose] def ea7ChkBits : Bool :=
  (List.range 32).all fun m => ea7Bits.contains m == (ea7Diff 0 m == 0 && ea7Diff 31899 m == 0)

@[expose] def ea7ChkW : Bool :=
  ea7Bits.all fun m => (List.range 75735).any fun i => wt i == 2 ^ m

@[expose] def ea7InX (p : Nat) : Bool := decide (p < 365211) && tvImg p 0 == 0 && tvImg p 31899 == 31899

@[expose] def ea7I : List Nat := (List.range 365211).filter ea7InX

@[expose] def ea7Restr (p : Nat) : List Nat :=
  let A := tvCols p
  ea7Bits.map fun m => applyCols A (2 ^ m)

@[expose] def ea7ChkF4 : Bool :=
  let R := ea7I.map fun p => (p, ea7Restr p)
  R.all fun a => R.all fun b => a.1 == b.1 || a.2 != b.2

@[expose] def ea7InF0 (p : Nat) : Bool := p == 0 || p == 31899 || ea7InX p

@[expose] def ea7Triple (k : Nat) : List Nat :=
  [(linePair k).1, (linePair k).2, (linePair k).1 ^^^ (linePair k).2]

@[expose] def ea7RigData : List (Nat × Nat × Nat) :=
  [(1, 0, 31), (2, 0, 557), (4, 1579, 1583), (8, 1579, 3675), (16, 1583, 3675), (32, 1591, 3683),
    (64, 557, 31899), (128, 31, 31899), (256, 3747, 7899), (512, 1655, 7963), (1024, 1719, 3811),
    (2048, 1847, 3939)]

@[expose] def ea7ChkRig : Bool :=
  (List.range 12).all (fun i => ea7RigData.any fun t => t.1 == 2 ^ i) &&
  ea7RigData.all fun t => ea7InF0 t.2.1 && ea7InF0 t.2.2 && (ea7Triple t.2.1).contains t.1 &&
    (ea7Triple t.2.2).contains t.1 &&
    (ea7Triple t.2.1).all fun y => !(ea7Triple t.2.2).contains y || y == t.1

@[expose] def ea7Elim (C : Array Nat) : Array (Nat × Nat) :=
  (List.range 32).foldl (fun (B : Array (Nat × Nat)) m =>
    let r := (List.range 32).reverse.foldl (fun (r : Nat × Nat) j =>
      if r.1.testBit j && (B[j]!).1 != 0 then (r.1 ^^^ (B[j]!).1, r.2 ^^^ (B[j]!).2) else r)
      (C[m]! ^^^ 2 ^ m, 2 ^ m)
    if r.1 == 0 then B else B.set! (Nat.log2 r.1) r) (Array.replicate 32 (0, 0))

@[expose] def ea7Solve (B : Array (Nat × Nat)) (x : Nat) : Nat :=
  let r := (List.range 32).reverse.foldl (fun (r : Nat × Nat) j =>
    if r.1.testBit j && (B[j]!).1 != 0 then (r.1 ^^^ (B[j]!).1, r.2 ^^^ (B[j]!).2) else r) (x, 0)
  if r.1 == 0 then r.2 else 2 ^ 32

@[expose] def ea7ChkF3 : Bool :=
  let A := tvCols 0
  let B := tvCols 31899
  let W := (List.range 75735).filter fun i => applyCols A (wt i) == wt i && applyCols B (wt i) == wt i
  ea7I.all fun p =>
    let C := tvCols p
    let E := ea7Elim C
    W.any fun i =>
      let c := ea7Solve E (wt i)
      decide (c < 2 ^ 32) && (applyCols C c ^^^ c == wt i)

@[expose] def ea7InY (bs : List Nat) (q : Nat) : Bool := ea7InX q && bs.all fun b => tvImg q b == b

def ea7Bfs (gens : List Nat) (b : Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate 365211 false
  let mut pts : Array Nat := #[b]
  let mut pr : Array Nat := #[0]
  let mut gn : Array Nat := #[0]
  seen := seen.set! b true
  let mut j := 0
  while j < pts.size do
    let a := pts[j]!
    for g in gens do
      let v := tvImg g a
      if v < 365211 && !seen[v]! then
        seen := seen.set! v true
        pts := pts.push v
        pr := pr.push j
        gn := gn.push g
    j := j + 1
  return (pts, pr, gn)

@[expose] def ea7TreeOK (inY : Nat → Bool) (b n : Nat) (t : Array Nat × Array Nat × Array Nat) : Bool :=
  decide (b < 365211) && decide (0 < n) && t.1.size == n && t.2.1.size == n && t.2.2.size == n &&
  t.1[0]! == b && (List.range n).all (fun j => decide (t.1[j]! < 365211)) &&
  (List.range n).all (fun j => j == 0 || (decide (t.2.1[j]! < j) && decide (t.2.2[j]! < 365211) &&
    inY t.2.2[j]! && tvImg t.2.2[j]! t.1[t.2.1[j]!]! == t.1[j]!)) &&
  (List.range n).all fun j => (List.range j).all fun j' => t.1[j']! != t.1[j]!

@[expose] def ea7Bases : List Nat := [142115, 8163, 303839, 31, 1083]

@[expose] def ea7Sizes : List Nat := [1575, 864, 128, 3, 2]

@[expose] def ea7Level (i : Nat) : Bool :=
  ea7TreeOK (ea7InY (ea7Bases.take i)) ea7Bases[i]! ea7Sizes[i]!
    (ea7Bfs (ea7I.filter (ea7InY (ea7Bases.take i))) ea7Bases[i]!)

@[expose] def ea7ChkChain : Bool := (List.range 5).all ea7Level

@[expose] def ea7IsA (a : Nat) : Bool := a == 31 || a == 557 || a == 1083

@[expose] def ea7ChkOdd : Bool :=
  ea7I.length == 1578 &&
  (ea7I.all fun a => ea7I.all fun q => ea7InX (tvImg q a) && ea7IsA (tvImg q a) == ea7IsA a) &&
  ea7InX 31 && ea7InX 557 && ea7InX 1083 && tvImg 557 31 == 1083 && tvImg 1083 31 == 557 &&
  ea7InX ea7Bases[0]! && !ea7IsA ea7Bases[0]!

end CFSG.SmithD6
