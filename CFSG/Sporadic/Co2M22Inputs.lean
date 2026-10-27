module

public import CFSG.Sporadic.Co2InvCheckInputs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Sporadic.Co2Heavy

open CFSG.Sporadic.Co2Inv CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def rowPerm (pt : Array UInt32) (X : Array ℕ) : Array ℕ :=
  let gt := transposeRows 22 X
  Array.ofFn (n := 2300) fun i => (pt[vecMulN 22 gt co2PackedVecs[i.val]!]!).toNat

@[expose] def rowCheck (levels : Array Level) (pt : Array UInt32) (X : Array ℕ) : Bool :=
  let gt := transposeRows 22 X
  let p := rowPerm pt X
  wfRows X && p.size == 2300 && isInvA 2300 p (invCand 2300 p) &&
    allLt 2300 (fun i => co2PackedVecs[p[i]!]! == vecMulN 22 gt co2PackedVecs[i]!) &&
    siftA 2300 levels co2BaseArr 0 p

@[expose] def wordRows (x y xi yi : Array ℕ) (w : List (ℕ × Bool)) : Array ℕ :=
  w.foldl (fun acc l => mulRows 22 acc
    (if l.1 = 0 then (if l.2 then x else xi) else (if l.2 then y else yi))) (idRows 22)

end CFSG.Sporadic.Co2Heavy
