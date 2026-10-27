module

public import Certificates.Data.SmithECheck
public import Certificates.Data.CFSGNative.Fischer.Hyperoval

public section

namespace CFSG.SmithE

open CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def uaAl : Array Nat := #[1, 4, 5, 9, 16, 17, 20, 25, 33, 13, 21, 29, 36, 37, 41, 45,
  49, 52, 53, 57, 61]

@[expose] def uaCo : Array Nat := #[1, 2, 4, 8, 16, 32, 64, 128, 256, 15, 119, 213, 233, 510, 347,
  423, 305, 187, 413, 451, 365]

@[expose] def uaVec (W : Nat × Nat × Nat) (a : Nat) : Nat :=
  scaleC (a % 4) W.1 ^^^ scaleC (a / 4 % 4) W.2.1 ^^^ scaleC (a / 16) W.2.2

@[expose] def uaPt (i k : Nat) : Nat := uPos[normC (uaVec (wB i) uaAl[k]!)]!

@[expose] def uaPts : Array (Array Nat) :=
  Array.ofFn (n := 891) fun i => Array.ofFn (n := 21) fun k => uaPt i.val k.val

@[expose] def uaAp (T : Array Table) (W : Array Nat) (a : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => uaAp T W a n (if a.testBit n then ap T[W[n]!]! x else x)

@[expose] def uaMem (W : Array Nat) (q : Nat) : Bool := anyIn 21 fun k => W[k]! == q

@[expose] def uaPos (W : Array Nat) (q : Nat) : Nat :=
  ((List.range 21).find? fun k => W[k]! == q).getD 21

@[expose] def uaPlaneOK (PT : Array Flags) (T : Array Table) (W : Array Nat) : Bool :=
  W.size == 21 &&
  allIn 0 21 (fun k => decide (W[k]! < 693)) &&
  allIn 0 21 (fun k => allIn 0 21 fun l => k == l || W[k]! != W[l]!) &&
  allIn 0 21 (fun k => allIn 0 21 fun l => PT[W[k]!]![W[l]!]!) &&
  allIn 0 693 (fun q => !(allIn 0 21 fun k => PT[W[k]!]![q]!) || uaMem W q) &&
  allIn 0 21 (fun k => allIn 0 693 fun x => uaAp T W uaCo[k]! 9 x == ap T[W[k]!]! x) &&
  allIn 1 512 (fun a => anyIn 693 fun x => uaAp T W a 9 x != x)

@[expose] def uaHypOK (PT : Array Flags) (T : Array Table) : Bool :=
  allIn 0 693 fun p => allIn 0 693 fun q => PT[p]![q]! || !PT[q]![ap T[p]! q]!

@[expose] def uaDistinctOK (P : Array (Array Nat)) : Bool :=
  allIn 0 891 fun i => allIn 0 891 fun j => i == j || anyIn 21 fun k => !uaMem P[j]! P[i]![k]!

@[expose] def uaMaskOK (P : Array (Array Nat)) : Bool :=
  allIn 0 891 fun i => allIn 0 693 fun q => (maskArr[i]!).testBit uPts[q]! == uaMem P[i]! q

@[expose] def chkUA (_ : Unit) : Bool :=
  let PT := perpTab ()
  let T := tvTabs
  let P := uaPts
  P.size == 891 && parAll 891 7 (fun i => uaPlaneOK PT T P[i]!) && uaHypOK PT T &&
    uaDistinctOK P && uaMaskOK P

end CFSG.SmithE
