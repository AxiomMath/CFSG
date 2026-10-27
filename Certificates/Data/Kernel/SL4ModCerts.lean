module

public import CFSG.LargeExtraspecial.SL4ModNativeSpin

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def mkCert (x : Array Nat × Array (Nat × Nat) × Bool × Nat × Array Nat) : SpinCert :=
  { L := x.1, src := x.2.1, big := x.2.2.1, sel := x.2.2.2.1, B := x.2.2.2.2 }

@[expose] def tabL (taus : Array (Array Nat)) : List (List Nat) := taus.toList.map Array.toList

@[expose] def bitsGo (g : Nat → Bool) : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | a :: t, k, acc => bitsGo g t (k + 1) (if g a then acc ||| (1 <<< k) else acc)

@[expose] def bitsL (g : Nat → Bool) (t : List Nat) : Nat :=
  if t.length = 105 then bitsGo g t 0 0 else ofBits 105 fun k => g (t.getD k 0)

@[expose] def actVL (t : List Nat) (x : Nat) : Nat := bitsL (fun a => x.testBit (a % 105)) t

@[expose] def expandL (lab : List Nat) (c : Nat) : Nat := bitsL c.testBit lab

@[expose] def xorGo : Nat → List Nat → Nat → Nat
  | _, [], acc => acc
  | m, a :: L, acc => xorGo (m / 2) L (if m.testBit 0 then acc ^^^ a else acc)

@[expose] def xorSelL (mask : Nat) (L : List Nat) : Nat := xorGo mask L 0

@[expose] def inSpanL (x : Nat) (B : List Nat) : Bool :=
  (List.range (2 ^ B.length)).any fun mask => xorSelL mask B == x

@[expose] def indep9L (L : List Nat) : Bool :=
  (List.range 512).all fun mask => mask == 0 || nz (xorSelL mask L)

@[expose] def derivOKL (tl : List (List Nat)) (m : Nat) (L : List Nat) (src : List (Nat × Nat)) :
    Bool :=
  L.getD 0 0 == m && (List.range L.length).all fun t => t == 0 ||
    (decide ((src.getD t (0, 0)).1 < 6) && decide ((src.getD t (0, 0)).2 < t) &&
      L.getD t 0 == actVL (tl.getD (src.getD t (0, 0)).1 []) (L.getD (src.getD t (0, 0)).2 0))

@[expose] def closedOKL (tl : List (List Nat)) (B : List Nat) : Bool :=
  (List.range B.length).all fun t => (List.range 6).all fun s =>
    inSpanL (actVL (tl.getD s []) (B.getD t 0)) B

@[expose] def validL (tl : List (List Nat)) (m : Nat) (c : SpinCert) : Bool :=
  derivOKL tl m c.L.toList c.src.toList &&
    (if c.big then decide (9 ≤ c.L.toList.length) && indep9L c.L.toList
    else nz (xorSelL c.sel c.L.toList) && decide (c.B.toList.length ≤ 7) &&
      inSpanL (xorSelL c.sel c.L.toList) c.B.toList && closedOKL tl c.B.toList)

@[expose] def checkSpinFrom (tl : List (List Nat)) (od : OrbData) : Nat → List SpinCert → Bool
  | _, [] => true
  | n, c :: cs => validL tl (expandL od.lab.toList n) c && checkSpinFrom tl od (n + 1) cs

@[expose] def checkSpinL (d : CosetData) (od : OrbData) (cs : List SpinCert) : Bool :=
  cs.length == 127 && checkSpinFrom (tabL d.tau) od 1 cs

end CFSG.LargeExtraspecial.SL4Mod.Native
