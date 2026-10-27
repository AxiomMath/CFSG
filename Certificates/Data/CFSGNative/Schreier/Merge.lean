module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Certificates.Native

open CFSG.Monster.B.Co2.Native

@[expose] def relabel (lab : Array Nat) (p q : Nat) : Array Nat :=
  let lq := lab[q]!
  let lp := lab[p]!
  lab.map fun l => if l == lq then lp else l

@[expose] def mergeInit (n b x : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => if i.val = x then b else i.val

@[expose] def mergeStep (n : Nat) (G : Array (Array Nat)) (st : Bool × Array Nat)
    (t : Nat × Nat × Nat) : Bool × Array Nat :=
  (st.1 && decide (t.1 < G.size) && decide (t.2.1 < n) && decide (t.2.2 < n) &&
      st.2[t.2.1]! == st.2[t.2.2]!,
    relabel st.2 (G[t.1]!)[t.2.1]! (G[t.1]!)[t.2.2]!)

@[expose] def mergeOK (n : Nat) (G : Array (Array Nat)) (b x : Nat)
    (L : List (Nat × Nat × Nat)) : Bool :=
  let st := L.foldl (mergeStep n G) (true, mergeInit n b x)
  decide (b < n) && decide (x < n) && st.1 && allLt n fun a => st.2[a]! == st.2[0]!

end CFSG.Certificates.Native
