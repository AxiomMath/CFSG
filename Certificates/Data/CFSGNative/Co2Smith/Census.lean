module

public import Certificates.Data.CFSGNative.Co2Smith.Check
public import Certificates.Data.CFSGNative.Co2Smith.Spin8

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def chainRowsN (seeds : Array (Array Nat)) (k : Nat) : Array (Array Nat) :=
  Array.map (mRows seeds) chainGens[k]!

@[expose] def chainRecN (seeds : Array (Array Nat)) (k : Nat) :
    Array Nat × Array Nat × Array Nat :=
  orbitBFS (vecStep (chainRowsN seeds k)) (chainRowsN seeds k).size chainBase[k]! 100

@[expose] def tRowsN (rec_ : Array Nat × Array Nat × Array Nat) (G : Array (Array Nat))
    (i : Nat) : Array Nat :=
  if i = 0 then idRows 22
  else if _hp : rec_.2.1[i]! < i then mulRows 22 G[rec_.2.2[i]!]! (tRowsN rec_ G rec_.2.1[i]!)
  else idRows 22
termination_by i

@[expose] def tArrN (seeds : Array (Array Nat)) : Array (Array (Array Nat)) :=
  (List.range 6).toArray.map fun k =>
    (List.range chainOrb[k]!).toArray.map (tRowsN (chainRecN seeds k) (chainRowsN seeds k))

@[expose] def sRowsN (T : Array (Array (Array Nat))) (n : Nat) : Array Nat :=
  mulRows 22 T[0]![n % 63]! (mulRows 22 T[1]![n / 63 % 32]! (mulRows 22 T[2]![n / 2016 % 15]!
    (mulRows 22 T[3]![n / 30240 % 8]! (mulRows 22 T[4]![n / 241920 % 3]!
      T[5]![n / 725760 % 2]!))))

@[expose] def aSpinN (_ : Unit := ()) : Array Int := wordZ (sp6Wa.map sCode)

@[expose] def bSpinN (_ : Unit := ()) : Array Int := wordZ (sp6Wb.map sCode)

@[expose] def mixSpinN (w : List Nat) : Array Int :=
  w.foldr (fun x acc => mulZ (if x == 2 then aSpinN else bSpinN) acc) idZ

@[expose] def tSpinN (rec_ : Array Nat × Array Nat × Array Nat) (G : Array (Array Int))
    (i : Nat) : Array Int :=
  if i = 0 then idZ
  else if _hp : rec_.2.1[i]! < i then mulZ G[rec_.2.2[i]!]! (tSpinN rec_ G rec_.2.1[i]!)
  else idZ
termination_by i

@[expose] def tSpinArrN (seeds : Array (Array Nat)) : Array (Array (Array Int)) :=
  (List.range 6).toArray.map fun k =>
    (List.range chainOrb[k]!).toArray.map
      (tSpinN (chainRecN seeds k) (Array.map mixSpinN chainGens[k]!))

@[expose] def sSpinN (T : Array (Array (Array Int))) (n : Nat) : Array Int :=
  mulZ T[0]![n % 63]! (mulZ T[1]![n / 63 % 32]! (mulZ T[2]![n / 2016 % 15]!
    (mulZ T[3]![n / 30240 % 8]! (mulZ T[4]![n / 241920 % 3]! T[5]![n / 725760 % 2]!))))

@[expose] def vecMulF (Y : Array Nat) (v : Nat) (j acc : Nat) : Nat :=
  if j < 22 then vecMulF Y v (j + 1) (if v.testBit j then acc ^^^ Y[j]! else acc) else acc
termination_by 22 - j

@[expose] def mulRowsF (X Y : Array Nat) : Array Nat := X.map fun v => vecMulF Y v 0 0

@[expose] def sRowsF (T : Array (Array (Array Nat))) (n : Nat) : Array Nat :=
  mulRowsF T[0]![n % 63]! (mulRowsF T[1]![n / 63 % 32]! (mulRowsF T[2]![n / 2016 % 15]!
    (mulRowsF T[3]![n / 30240 % 8]! (mulRowsF T[4]![n / 241920 % 3]! T[5]![n / 725760 % 2]!))))

@[expose] def qRowsN (seeds : Array (Array Nat)) (e : Nat) : Array Nat :=
  nfRows seeds (hRows seeds) (e / 256) (e % 256)

@[expose] def mulP (a b : Array Nat × Array Int) : Array Nat × Array Int :=
  (mulRowsF a.1 b.1, mulZ a.2 b.2)

@[expose] def negZ (X : Array Int) : Array Int := X.map fun a => -a

@[expose] def eqvP (z0R : Array Nat) (a b : Array Nat × Array Int) : Bool :=
  (a.2 == b.2 && a.1 == b.1) || (a.2 == negZ b.2 && a.1 == mulRowsF b.1 z0R)

@[expose] def repP (Q : Array (Array Nat)) (T : Array (Array (Array Nat)))
    (TS : Array (Array (Array Int))) (e n : Nat) : Array Nat × Array Int :=
  (mulRowsF (sRowsF T n) Q[e]!, sSpinN TS n)

@[expose] def cntP (Q : Array (Array Nat)) (T : Array (Array (Array Nat)))
    (TS : Array (Array (Array Int))) (ns : List Nat) (P : Array Nat × Array Int → Bool) : Nat :=
  ns.foldl (fun acc n =>
    let S := sRowsF T n
    let X := sSpinN TS n
    acc + ((List.range 512).filter fun e => P (mulRowsF S Q[e]!, X)).length) 0

@[expose] def hashP (b : Array Nat × Array Int) : Nat :=
  let r := b.1.foldl (fun acc x => (acc * 1000003 + x) % 18446744073709551557) 0
  b.2.foldl (fun acc x => (acc * 1000033 + (x + 128).toNat) % 18446744073709551557) r

@[expose] def keyP (z0R : Array Nat) (a : Array Nat × Array Int) : Nat :=
  min (hashP a) (hashP (mulRowsF a.1 z0R, negZ a.2))

@[expose] def conjP (g gi y : Array Nat × Array Int) : Array Nat × Array Int :=
  mulP (mulP g y) gi

@[expose] def bfsP (z0R : Array Nat) (G Gi : Array (Array Nat × Array Int))
    (start : Array Nat × Array Int) (cap : Nat) :
    Array (Array Nat × Array Int) × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (keyP z0R start) 0
  let mut pts : Array (Array Nat × Array Int) := #[start]
  let mut par : Array Nat := #[0]
  let mut let_ : Array Nat := #[0]
  let mut i := 0
  for _ in [0:cap] do
    if i < pts.size then
      let x := pts[i]!
      for l in [0:G.size] do
        let y := conjP G[l]! Gi[l]! x
        let k := keyP z0R y
        if !seen.contains k then
          seen := seen.insert k pts.size
          pts := pts.push y
          par := par.push i
          let_ := let_.push l
      i := i + 1
  return (pts, par, let_)

@[expose] def treeP (z0R : Array Nat) (G Gi : Array (Array Nat × Array Int))
    (start : Array Nat × Array Int) (n : Nat)
    (rec_ : Array (Array Nat × Array Int) × Array Nat × Array Nat) : Bool :=
  let pts := rec_.1
  let par := rec_.2.1
  let let_ := rec_.2.2
  let pm : Std.HashMap Nat Nat := Id.run do
    let mut m : Std.HashMap Nat Nat := ∅
    for i in [0:pts.size] do
      m := m.insert (keyP z0R pts[i]!) i
    return m
  pts.size == n && par.size == n && let_.size == n && pts[0]! == start &&
    (List.range n).all fun i =>
      pm.getD (keyP z0R pts[i]!) n == i &&
      (i == 0 || (par[i]! < i && let_[i]! < G.size &&
        pts[i]! == conjP G[let_[i]!]! Gi[let_[i]!]! pts[par[i]!]!))

@[expose] def powP (a : Array Nat × Array Int) : Nat → Array Nat × Array Int
  | 0 => (idRows 22, idZ)
  | k + 1 => mulP (powP a k) a

@[expose] def invP (a : Array Nat × Array Int) : Array Nat × Array Int :=
  ((List.range 100).find? fun m => powP a (m + 1) == (idRows 22, idZ)).elim (idRows 22, idZ)
    fun m => powP a m

@[expose] def hpReps (_ : Unit := ()) : List (Nat × Nat) := [(1, 0), (0, 2331), (2, 2331), (0, 144)]

@[expose] def hpSqZ (_ : Unit := ()) : List Nat := [5376, 1152, 448, 96]

@[expose] def hpSqR (_ : Unit := ()) : List Nat := [5376, 768, 128, 0]

@[expose] def hpCls (_ : Unit := ()) : List Nat := [270, 2520, 22680, 120960]

structure HPData where
  T : Array (Array (Array Nat))
  TS : Array (Array (Array Int))
  Q : Array (Array Nat)
  SQ : Array (Array Nat)
  L : List Nat

@[expose] def sqArrN (T : Array (Array (Array Nat))) : Array (Array Nat) :=
  Array.ofFn (n := 1451520) fun n => let S := sRowsF T n.val; mulRowsF S S

@[expose] def hpData (seeds : Array (Array Nat)) : HPData :=
  let T := tArrN seeds
  let SQ := sqArrN T
  { T := T, TS := tSpinArrN seeds, Q := (List.range 512).toArray.map (qRowsN seeds), SQ := SQ,
    L := (List.range 1451520).filter fun n => SQ[n]! == idRows 22 }

@[expose] def hpGens (seeds : Array (Array Nat)) : Array (Array Nat × Array Int) :=
  #[(mRows seeds [2], aSpinN), (mRows seeds [3], bSpinN), ((hRows seeds)[0]!, idZ)]

@[expose] def hpGensOK (seeds : Array (Array Nat)) : Bool :=
  let G := hpGens seeds
  (List.range 3).all fun l =>
    mulP G[l]! (invP G[l]!) == (idRows 22, idZ) && validM (invP G[l]!).1 &&
      (invP G[l]!).2.size == 64

@[expose] def hpInvOK (z0R : Array Nat) (D : HPData) : Bool :=
  cntP D.Q D.T D.TS D.L (fun y => eqvP z0R (mulP y y) (idRows 22, idZ)) == 146432

@[expose] def hpSqrtOK (z0R : Array Nat) (D : HPData) (i : Nat) : Bool :=
  let r := repP D.Q D.T D.TS hpReps[i]!.1 hpReps[i]!.2
  let nr := hpReps[i]!.2
  let Sr := sRowsF D.T nr
  let gate := if nr == 0 then D.L else
    D.L.filter fun n => let S := sRowsF D.T n; mulRowsF S Sr == mulRowsF Sr S
  let ns := if nr == 0 then D.L else (List.range 1451520).filter fun n => D.SQ[n]! == Sr
  eqvP z0R (mulP r r) (idRows 22, idZ) && !eqvP z0R r (idRows 22, idZ) && !eqvP z0R r (z0R, idZ) &&
  cntP D.Q D.T D.TS gate (fun y => eqvP z0R (mulP y y) (z0R, idZ) && eqvP z0R (mulP y r) (mulP r y))
      == hpSqZ[i]! &&
    cntP D.Q D.T D.TS ns (fun y => eqvP z0R (mulP y y) r && eqvP z0R (mulP y r) (mulP r y)) ==
      hpSqR[i]!

@[expose] def hpOrbitOK (z0R : Array Nat) (D : HPData) (G : Array (Array Nat × Array Int))
    (i : Nat) : Bool :=
  let r := repP D.Q D.T D.TS hpReps[i]!.1 hpReps[i]!.2
  let Gi := G.map invP
  treeP z0R G Gi r hpCls[i]! (bfsP z0R G Gi r 200000)

@[expose] def hpEOK (z0R : Array Nat) (D : HPData) : Bool :=
  let rep := fun (e : Nat) => repP D.Q D.T D.TS e 0
  let one : Array Nat × Array Int := (idRows 22, idZ)
  ((List.range 512).all fun e =>
    let a := rep e
    (!((List.range 512).all fun e' => let b := rep e'; eqvP z0R (mulP a b) (mulP b a)) ||
      e == 0 || e == 256) &&
    (List.range 512).all fun e' => let b := rep e';
      eqvP z0R (mulP a b) (mulP b a) || eqvP z0R (mulP a b) (mulP (z0R, idZ) (mulP b a))) &&
  (let t := rep 1; let a := rep 2; let b := rep 32
    eqvP z0R (mulP a a) one && eqvP z0R (mulP b b) one && eqvP z0R (mulP a t) (mulP t a) &&
      eqvP z0R (mulP b t) (mulP t b) && !eqvP z0R (mulP a b) (mulP b a))

@[expose] def hpCensusOK (seeds : Array (Array Nat)) : Bool :=
  let D := hpData seeds
  let z0R := seeds[0]!
  hpGensOK seeds && hpInvOK z0R D &&
    ((List.range 4).all fun i => hpSqrtOK z0R D i && hpOrbitOK z0R D (hpGens seeds) i) &&
    hpEOK z0R D

end CFSG.Sporadic.Co2Smith.Native
