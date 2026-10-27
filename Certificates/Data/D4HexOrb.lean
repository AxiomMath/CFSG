module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.D4Hex

open CFSG.Monster.B.Co2.Native

structure OrbRec where
  ord : Array Nat
  par : Array Nat
  lab : Array Nat
  pos : Array Nat

@[expose] def orbBFS (N k : Nat) (actF : Nat → Nat → Nat) (root : Nat) : OrbRec := Id.run do
  let mut pos : Array Nat := (Array.replicate N N).set! root 0
  let mut ord : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:N] do
    if h < ord.size then
      let x := ord[h]!
      for j in [0:k] do
        let y := actF j x
        if y < N && pos[y]! == N then
          pos := pos.set! y ord.size
          ord := ord.push y
          par := par.push h
          lab := lab.push j
  return ⟨ord, par, lab, pos⟩

@[expose] def orbOK (N k : Nat) (actF : Nat → Nat → Nat) (root cnt : Nat) (items : Nat → Bool)
    (r : OrbRec) : Bool :=
  r.ord.size == cnt && r.par.size == cnt && r.lab.size == cnt && r.ord[0]! == root &&
    (allLt cnt fun i => decide (r.ord[i]! < N)) &&
    (allLt cnt fun i => i == 0 || (decide (r.par[i]! < i) && decide (r.lab[i]! < k) &&
      actF r.lab[i]! r.ord[r.par[i]!]! == r.ord[i]!)) &&
    allLt N fun x => !items x || (decide (r.pos[x]! < cnt) && r.ord[r.pos[x]!]! == x)

@[expose] def orbCheck (N k : Nat) (actF : Nat → Nat → Nat) (root cnt : Nat) (items : Nat → Bool) :
    Bool :=
  orbOK N k actF root cnt items (orbBFS N k actF root)

end CFSG.D4Hex
