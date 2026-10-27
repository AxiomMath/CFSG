module

public import Certificates.Data.CFSGNative.GF2W1112.Spin

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native

def w12SpinSearch (nGen : Nat) (ap : Nat → Nat → Nat) (v x target : Nat) :
    Array W12Op × Array Nat := Id.run do
  let mut regs : Array Nat := #[v, x]
  let mut ops : Array W12Op := #[]
  let mut bpiv : Array Nat := #[Nat.log2 v]
  let mut breg : Array Nat := #[0]
  let (r1, o1, c1) := w12Reduce regs ops bpiv breg 1
  regs := r1
  ops := o1
  let x' := regs[c1]!
  if x' == 0 then
    return (ops, breg)
  bpiv := bpiv.push (Nat.log2 x')
  breg := breg.push c1
  let mut queue : Array Nat := #[c1]
  let mut qi := 0
  while qi < queue.size && bpiv.size < target do
    let u := queue[qi]!
    qi := qi + 1
    for k in [0:nGen] do
      if bpiv.size < target then
        regs := regs.push (ap k regs[u]!)
        ops := ops.push (W12Op.app k u)
        let (r2, o2, c2) := w12Reduce regs ops bpiv breg (regs.size - 1)
        regs := r2
        ops := o2
        let r := regs[c2]!
        if r != 0 then
          bpiv := bpiv.push (Nat.log2 r)
          breg := breg.push c2
          queue := queue.push c2
  return (ops, breg)

@[expose] def w12LeadsOK (regs : Array Nat) (idx : List Nat) : Bool :=
  idx.all (fun i => decide (i < regs.size) && regs[i]! != 0) &&
    decide ((idx.map fun i => Nat.log2 regs[i]!).Nodup)

@[expose] def w12IrrOne (nGen : Nat) (ap : Nat → Nat → Nat) (v x target : Nat) : Bool :=
  let r := w12SpinSearch nGen ap v x target
  decide (target ≤ r.2.size) && w12LeadsOK (w12Run nGen ap #[v, x] r.1.toList) r.2.toList

@[expose] def w12IrrAll (nGen : Nat) (ap : Nat → Nat → Nat) (bN : Nat → Nat → Bool)
    (v n target : Nat) : Bool :=
  w12AllLoop (fun x =>
    x.testBit (Nat.log2 v) || x == 0 || bN x v || w12IrrOne nGen ap v x target) n 0

@[expose] def w12Irr (d : Nat) (gens : Array (Array Nat)) (ft : Array Nat) (v n target : Nat) :
    Bool :=
  w12IrrAll gens.size (w12Ap d gens) (w12BN d ft) v n target

end CFSG.GF2W1112
