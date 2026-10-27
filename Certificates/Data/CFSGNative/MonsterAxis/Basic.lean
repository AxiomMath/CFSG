module

public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Std.Data.HashMap

public section

namespace CFSG.Monster.AxisCount.Native

open CFSG.Monster.B.Rep4371.Native

set_option compiler.extract_closed false

@[expose] def offX (_ : Unit := ()) : Nat := 300

@[expose] def offW (_ : Unit := ()) : Nat := 98580

@[expose] def nTot (_ : Unit := ()) : Nat := 196884

@[expose] def pairIdx (i j : Nat) : Nat := i * (47 - i) / 2 + (j - i - 1)

@[expose] def aIdx (i j : Nat) : Nat :=
  if i = j then i else 24 + pairIdx (min i j) (max i j)

@[expose] def pairTab (_ : Unit := ()) : Array (Nat × Nat) :=
  ((List.range 24).flatMap fun i => ((List.range 24).filter fun j => i < j).map fun j => (i, j)).toArray

@[expose] def aPos (z : Nat) : Nat × Nat := if z < 24 then (z, z) else pairTab[z - 24]!

@[expose] def rowIdx (η : Bool) (c : Nat) : Nat := (if η then 2048 else 0) + pi0N c / 2 % 2048

@[expose] def rowEta (r : Nat) : Bool := decide (2048 ≤ r)

@[expose] def rowC (r : Nat) : Nat := 2 * (r % 2048)

@[expose] def octTab (_ : Unit := ()) : Array Nat :=
  ((List.range 4096).filter fun a => popcN 24 (wordN a) == 8).toArray

@[expose] def evenTab (_ : Unit := ()) : Array Nat :=
  ((List.range 128).filter fun m => popcN 8 m % 2 == 0).toArray

@[expose] def suppList (w : Nat) : List Nat := (List.range 24).filter fun i => w.testBit i

@[expose] def spreadG (w m : Nat) : Nat := combN (fun t => 2 ^ (suppList w).getD t 0) 8 m

@[expose] def octCodeG (a m : Nat) : Nat :=
  a ^^^ (if popcN 24 (spreadG (wordN a) m) / 2 % 2 == 1 then 63 else 0)

@[expose] def thetaTab (_ : Unit) : Array Nat := (Array.range 4096).map thetaN

@[expose] def keyAt (th : Array Nat) (p : Nat) : Nat × Nat :=
  if p < 552 then
    let t := pairTab[p / 2]!
    (if p % 2 = 0 then 0 else 63, dualN (2 ^ t.1 ||| 2 ^ t.2))
  else if p < 49704 then
    let q := p - 552
    let a := oddCode (2 * (q / 24)) (q % 24)
    (a, th[a]! ^^^ dualN (2 ^ (q % 24)))
  else
    let q := p - 49704
    let a := octTab[q / 64]!
    let m := evenTab[q % 64]!
    let b := octCodeG a m
    (b, th[b]! ^^^ dualN (spreadG (wordN a) m))

@[expose] def keyCode (a d : Nat) : Nat := a % 4096 * 4096 + d % 4096

structure TauTab where
  S : Array Int
  w : Array Nat
  pb : Array Bool

@[expose] def mkTauTab (_ : Unit) : TauTab :=
  ⟨Array.ofFn (n := 4096) fun k => octSign evenTab[k.val / 64]! evenTab[k.val % 64]!,
    Array.ofFn (n := 2048) fun t => wordN (2 * t.val),
    Array.ofFn (n := 2048) fun t => pN (2 * t.val)⟩

structure Ctx where
  keys : Array (Nat × Nat)
  pos : Std.HashMap Nat Nat
  tau : TauTab
  th : Array Nat

@[expose, noinline] def mkKeys (th : Array Nat) : Array (Nat × Nat) :=
  (Array.range 98280).map (keyAt th)

@[expose, noinline] def mkPos (keys : Array (Nat × Nat)) : Std.HashMap Nat Nat :=
  (List.range 98280).foldl (fun m p => m.insert (keyCode keys[p]!.1 keys[p]!.2) p) ∅

@[expose, noinline] def mkCtxOf (th : Array Nat) (tau : TauTab) : Ctx :=
  let keys := mkKeys th
  ⟨keys, mkPos keys, tau, th⟩

@[expose] def mkCtx (_ : Unit) : Ctx := mkCtxOf (thetaTab ()) (mkTauTab ())

@[expose] def Ctx.find (c : Ctx) (a d : Nat) : Nat := c.pos.getD (keyCode a d) 98280

@[expose] def ctxCheck (c : Ctx) : Bool :=
  c.keys.size == 98280 && (List.range 98280).all fun p =>
    c.keys[p]!.1 < 4096 && c.keys[p]!.2 < 4096 && c.find c.keys[p]!.1 c.keys[p]!.2 == p

@[expose] def scatterAt (off n : Nat) (T : Nat → List (Nat × Int)) (D : Array Int) : Array Int :=
  (List.range n).foldl (fun out p =>
      let x := D[off + p]!
      if x == 0 then out
      else (T p).foldl
        (fun out' t => if t.1 < n then out'.modify t.1 (fun y => y + t.2 * x) else out') out)
    (Array.replicate n 0)

@[expose] def mmA (P Q : Array Int) : Array Int :=
  Array.ofFn (n := 576) fun ij =>
    sumRange (fun k => P[ij.val / 24 * 24 + k]! * Q[k * 24 + ij.val % 24]!) 24

@[expose] def trA (P : Array Int) : Array Int :=
  Array.ofFn (n := 576) fun ij => P[ij.val % 24 * 24 + ij.val / 24]!

@[expose] def aFull (D : Array Int) : Array Int :=
  Array.ofFn (n := 576) fun ij => D[aIdx (ij.val / 24) (ij.val % 24)]!

@[expose] def latA (G D : Array Int) : Array Int :=
  let R := mmA (trA G) (mmA (aFull D) G)
  Array.ofFn (n := 300) fun z => R[(aPos z).1 * 24 + (aPos z).2]!

@[expose] def wMul (G D : Array Int) : Array Int :=
  Array.ofFn (n := 98304) fun k =>
    sumRange (fun j => D[98580 + k / 24 * 24 + j]! * G[j * 24 + k % 24]!) 24

@[expose] def tabT (f : Pauli → Pauli) : Array Pauli := (Array.range 4096).map fun a => f (false, a, 0)

@[expose] def tabD (f : Pauli → Pauli) : Array Pauli := (Array.range 4096).map fun d => f (false, 0, d)

@[expose] def fastAct (tT tD : Array Pauli) (y : Pauli) : Pauli :=
  Pauli.mul (y.1, 0, 0) (Pauli.mul tT[y.2.1 % 4096]! tD[y.2.2 % 4096]!)

@[expose] def betaTab (p : Array Nat) : Array Bool :=
  Array.ofFn (n := 144) fun k => betaPN p (k.val / 12) (k.val % 12)

@[expose] def kappaT (bt : Array Bool) (a : Nat) : Bool :=
  xorSum (fun i => xorSum (fun j =>
    decide (i < j) && a.testBit i && a.testBit j && bt[12 * i + j]!) 12) 12

@[expose] def tabTPerm (p : Array Nat) (bt : Array Bool) (th : Array Nat) : Array Pauli :=
  (Array.range 4096).map fun a => (kappaT bt a, permCN p a, th[permCN p a]! ^^^ permDN p th[a]!)

@[expose] def tabDPerm (p : Array Nat) (th : Array Nat) : Array Pauli :=
  (Array.range 4096).map fun d =>
    (false ^^ kappaN p 0, permCN p 0, th[permCN p 0]! ^^^ permDN p (th[0]! ^^^ d))

@[expose] def ePermT (p : Array Nat) (bt : Array Bool) (η : Bool) (c : Nat) : Bool × Bool × Nat :=
  (kappaT bt (pi0N c) ^^ ((η ^^ kappaT bt 63) && mu0N (permCN p (pi0N c))), η ^^ kappaT bt 63,
    pi0N (permCN p (pi0N c)))

@[expose] def monoRows (rm : Bool → Nat → Bool × Bool × Nat) : Array (List (Nat × Int)) :=
  (Array.range 4096).map fun r =>
    let t := rm (rowEta r) (rowC r)
    [(rowIdx t.2.1 t.2.2, sgnI t.1)]

@[expose] def xiRows (_ : Unit) : Array (List (Nat × Int)) :=
  (Array.range 4096).map fun r =>
    [false, true].flatMap fun f =>
      let α := xiGammaN (rowC r) f
      if α == 0 then []
      else (List.range 64).map fun ν =>
        let t := xiGTerm (rowEta r != f) (rowC r) ν
        (rowIdx t.2.1 t.2.2, α * sgnI t.1)

@[expose] def idG (_ : Unit := ()) : Array Int :=
  Array.ofFn (n := 576) fun k => if k.val / 24 = k.val % 24 then 1 else 0

@[expose] def permG (arr : Array Nat) : Array Int :=
  Array.ofFn (n := 576) fun k => if arr[k.val / 24]! = k.val % 24 then 1 else 0

@[expose] def signG (a : Nat) : Array Int :=
  Array.ofFn (n := 576) fun k =>
    if k.val / 24 = k.val % 24 then sgnI ((wordN a).testBit (k.val % 24)) else 0

@[expose] def xiG (_ : Unit := ()) : Array Int :=
  Array.ofFn (n := 576) fun k =>
    if k.val / 24 / 4 = k.val % 24 / 4 then c4N (k.val / 24 % 4) (k.val % 24 % 4) / 32 else 0

@[expose] def tabCheck (_ : Unit) : Bool :=
  pairTab.size == 276 &&
  (List.range 276).all (fun tp =>
    pairTab[tp]!.1 < pairTab[tp]!.2 && pairTab[tp]!.2 < 24 &&
      pairIdx pairTab[tp]!.1 pairTab[tp]!.2 == tp) &&
  (List.range 24).all (fun i => (List.range 24).all fun j =>
    aIdx i j < 300 && aPos (aIdx i j) == (min i j, max i j)) &&
  octTab.size == 759 &&
  (List.range 759).all (fun o => octTab[o]! < 4096 && popcN 24 (wordN octTab[o]!) == 8) &&
  evenTab.size == 64 &&
  (List.range 64).all (fun q => evenTab[q]! < 128 && popcN 8 evenTab[q]! % 2 == 0)

@[expose] def octCheck (_ : Unit) : Bool :=
  (List.range 759).all fun o =>
    let w := wordN octTab[o]!
    let S := Array.ofFn (n := 256) fun m => spreadG w m.val
    (List.range 256).all (fun m =>
      (S[m]! &&& w == S[m]!) && popcN 24 S[m]! == popcN 8 m && S[m ^^^ 255]! == S[m]! ^^^ w) &&
    (List.range 256).all fun m => (List.range 256).all fun m' =>
      S[m &&& m']! == (S[m]! &&& S[m']!) && (m == m' || S[m]! != S[m']!)

end CFSG.Monster.AxisCount.Native
