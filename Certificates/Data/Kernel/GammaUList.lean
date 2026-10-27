module

public import Certificates.Data.CFSGNative.GammaU.Pairs

public section

namespace Certificates.Kernel.GammaUList

open CFSG.GammaU.Native

@[expose] def appL : List Nat → Nat → Nat
  | [], _ => 0
  | r :: l, n => Nat.xor (Nat.mul (Nat.mod n 2) r) (appL l (Nat.div n 2))

@[expose] def mulL (g h : List Nat) : List Nat := h.map (appL g)

@[expose] def idL : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

@[expose] def isoB (r : List Nat) : Bool :=
  r.length == 12 && r.all (· < 4096) &&
    (List.range 12).all (fun j => q0b r[j]! == q0b (2 ^ j)) &&
    (List.range 12).all fun i => (List.range 12).all fun j =>
      f0b r[i]! r[j]! == f0b (2 ^ i) (2 ^ j)

@[expose] def unitaryL (r : List Nat) : Bool :=
  (List.range 12).all fun j => appL r (theta0N (2 ^ j)) == theta0N (appL r (2 ^ j))

@[expose] def antiL (r : List Nat) : Bool :=
  (List.range 12).all fun j => appL r (theta0N (2 ^ j)) == theta0N (theta0N (appL r (2 ^ j)))

@[expose] def gammaUL (r : List Nat) : Bool := isoB r && (unitaryL r || antiL r)

@[expose] def subsetProductsL (gens : List (List Nat)) : List (List Nat) :=
  gens.foldl (fun acc g => acc ++ acc.map (mulL g)) [idL]

@[expose] def compOfL (c : Nat) : List (List Nat) :=
  subsetProductsL ((List.range 5).map fun i =>
    if c.testBit i then mulL k0.toList cBasis[i]!.toList else cBasis[i]!.toList)

@[expose] def nlOKAtL (S : List Nat) (C : List (List Nat)) (W : List (List Nat × List Nat)) : Bool :=
  W.all fun (g, gi) =>
    gammaUL g && gammaUL gi && mulL g gi == idL && mulL gi g == idL && appL g a0 == a0 &&
      d0.all (fun d => S.contains (appL g d)) && d0.all (fun d => S.contains (appL gi d)) &&
      C.all (fun x => C.contains (mulL (mulL g x) gi)) &&
      C.all (fun x => C.contains (mulL (mulL gi x) g))

@[expose] def invP (c : List Nat) : Nat → List Nat → List Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := mulL c x
    if y == idL then x else invP c fuel y

@[expose] def invOK (c r : List Nat) : Bool :=
  c.length == 12 && c.all (· < 4096) && r.length == 12 && r.all (· < 4096) &&
    mulL c r == idL && mulL r c == idL

@[expose] def invL (c : List Nat) : List Nat := invP c 64 idL

@[expose] def resConjCheckL : Bool :=
  [0, 1].all fun i =>
    let R := (resConj i).map Array.toList
    R.all (fun c => invOK c (invL c)) && (compOfL i).all (fun x => x.length == 12) &&
      nlOKAtL (spanList d0) (compOfL i) (R.map fun c => (c, invL c))

end Certificates.Kernel.GammaUList
