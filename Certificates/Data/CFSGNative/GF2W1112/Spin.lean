module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native

inductive W12Op where
  | app (k j : Nat)
  | add (i j : Nat)
  deriving Inhabited

@[expose] def w12Step (nGen : Nat) (ap : Nat → Nat → Nat) (regs : Array Nat) :
    W12Op → Array Nat
  | .app k j => regs.push (if k < nGen then ap k regs[j]! else 0)
  | .add i j => regs.push (regs[i]! ^^^ regs[j]!)

@[expose] def w12Run (nGen : Nat) (ap : Nat → Nat → Nat) (init : Array Nat)
    (ops : List W12Op) : Array Nat :=
  ops.foldl (w12Step nGen ap) init

@[expose] def w12AllLoop (p : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i => if p i then w12AllLoop p fuel (i + 1) else false

def w12Reduce (regs0 : Array Nat) (ops0 : Array W12Op) (bpiv breg : Array Nat) (cur0 : Nat) :
    Array Nat × Array W12Op × Nat := Id.run do
  let mut regs := regs0
  let mut ops := ops0
  let mut cur := cur0
  for i in [0:bpiv.size] do
    if regs[cur]!.testBit bpiv[i]! then
      regs := regs.push (regs[cur]! ^^^ regs[breg[i]!]!)
      ops := ops.push (W12Op.add cur breg[i]!)
      cur := regs.size - 1
  return (regs, ops, cur)

def w12SumOps (ops0 : Array W12Op) (regs0 breg : Array Nat) (mask : Nat) : Array W12Op :=
  Id.run do
    let mut regs := regs0
    let mut ops := ops0
    let mut cur : Nat := 0
    let mut first := true
    for i in [0:breg.size] do
      if mask.testBit i then
        if first then
          cur := breg[i]!
          first := false
        else
          regs := regs.push (regs[cur]! ^^^ regs[breg[i]!]!)
          ops := ops.push (W12Op.add cur breg[i]!)
          cur := regs.size - 1
    return ops

def w12Search (nGen : Nat) (ap : Nat → Nat → Nat) (qN : Nat → Bool) (bN : Nat → Nat → Bool)
    (goodN : Nat → Bool) (v x : Nat) : Array W12Op := Id.run do
  let mut regs : Array Nat := #[v, x]
  let mut ops : Array W12Op := #[]
  let mut bpiv : Array Nat := #[Nat.log2 v]
  let mut breg : Array Nat := #[0]
  let mut done := false
  let (r1, o1, c1) := w12Reduce regs ops bpiv breg 1
  regs := r1
  ops := o1
  let x' := regs[c1]!
  if x' == 0 then
    return ops
  bpiv := bpiv.push (Nat.log2 x')
  breg := breg.push c1
  let mut queue : Array Nat := #[c1]
  let mut qi := 0
  while qi < queue.size && !done do
    let u := queue[qi]!
    qi := qi + 1
    for k in [0:nGen] do
      if !done then
        regs := regs.push (ap k regs[u]!)
        ops := ops.push (W12Op.app k u)
        let (r2, o2, c2) := w12Reduce regs ops bpiv breg (regs.size - 1)
        regs := r2
        ops := o2
        let r := regs[c2]!
        if r != 0 then
          if qN r then
            done := true
          else
            for i in [0:breg.size] do
              if !done && bN r regs[breg[i]!]! then
                regs := regs.push (r ^^^ regs[breg[i]!]!)
                ops := ops.push (W12Op.add c2 breg[i]!)
                done := true
            if !done then
              bpiv := bpiv.push (Nat.log2 r)
              breg := breg.push c2
              queue := queue.push c2
  if done then
    return ops
  let m := breg.size
  let mut found := false
  let mut mask := 1
  let mut best := 0
  while mask < 2 ^ m && !found do
    let mut s := 0
    for i in [0:m] do
      if mask.testBit i then
        s := s ^^^ regs[breg[i]!]!
    if goodN s && s != v then
      found := true
      best := mask
    mask := mask + 1
  if found then
    return w12SumOps ops regs breg best
  return ops

@[expose] def w12Fast (nGen : Nat) : List (List W12Op) :=
  (List.range nGen).map (fun k => [W12Op.app k 1, W12Op.add 1 2]) ++
  (List.range nGen).flatMap (fun k => (List.range nGen).map fun l =>
    [W12Op.app k 1, W12Op.app l 2, W12Op.add 1 3])

@[expose] def w12Wit (nGen : Nat) (ap : Nat → Nat → Nat) (qN : Nat → Bool) (goodN : Nat → Bool)
    (v x : Nat) (ops : List W12Op) : Bool :=
  (w12Run nGen ap #[v, x] ops).any fun r => qN r || (goodN r && r != v)

@[expose] def w12CheckOne (nGen : Nat) (ap : Nat → Nat → Nat) (qN : Nat → Bool)
    (bN : Nat → Nat → Bool) (goodN : Nat → Bool) (v x : Nat) : Bool :=
  (w12Fast nGen).any (w12Wit nGen ap qN goodN v x) ||
    w12Wit nGen ap qN goodN v x (w12Search nGen ap qN bN goodN v x).toList

@[expose] def w12F3 (nGen : Nat) (ap : Nat → Nat → Nat) (qN : Nat → Bool)
    (bN : Nat → Nat → Bool) (goodN : Nat → Bool) (v n : Nat) : Bool :=
  w12AllLoop (fun x =>
    x.testBit (Nat.log2 v) || x == 0 || bN x v || qN x || w12CheckOne nGen ap qN bN goodN v x)
    n 0

@[expose] def w12Dot (d x y : Nat) : Bool :=
  (List.range d).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) false

@[expose] def w12Ap (d : Nat) (gens : Array (Array Nat)) (k x : Nat) : Nat :=
  vecMulN d gens[k]! x

@[expose] def w12QN (d : Nat) (qt : Array Nat) (x : Nat) : Bool := w12Dot d x (vecMulN d qt x)

@[expose] def w12BN (d : Nat) (ft : Array Nat) (x y : Nat) : Bool := w12Dot d x (vecMulN d ft y)

@[expose] def w12InPts (pts : Array Nat) (pos : Array UInt32) (n w : Nat) : Bool :=
  decide ((pos[w]!).toNat < n) && pts[(pos[w]!).toNat]! == w

@[expose] def w12Check (d : Nat) (gens : Array (Array Nat)) (qt ft pts : Array Nat)
    (pos : Array UInt32) (npts v n : Nat) : Bool :=
  w12F3 gens.size (w12Ap d gens) (w12QN d qt) (w12BN d ft) (w12InPts pts pos npts) v n

end CFSG.GF2W1112
