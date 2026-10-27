module

public import Certificates.Data.GH74EvSporCheck
public meta import Certificates.Data.GH74EvSporCheck

public section

namespace CFSG.GH74.Generic.S45.EvSpor

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.J2Cover

@[expose] def evalWord (n : Nat) (gs : Array Table) (w : List Nat) : Table :=
  w.foldl (fun acc i => compT n acc (if i < gs.size then gs[i]! else invT n gs[i - gs.size]!))
    (idT n)

@[expose] def j2CG : Array Table := j2Row2A.centGens.toArray

@[expose] def j2TA : Table := j2Row2A.rep

@[expose] def j2EWords : List (List Nat) := [[2, 2, 2], [3, 3, 3], [0, 3, 3, 3, 0], [1, 3, 3, 3, 1]]

@[expose] def j2EGens : List Table := j2EWords.map (evalWord 315 j2CG)

@[expose] def j2E : Array Table := closArr 315 cap j2EGens

@[expose] def commutatorT (n : Nat) (x y : Table) : Table :=
  compT n (compT n x y) (compT n (invT n x) (invT n y))

@[expose] def j2EEnumOK : Bool :=
  enumOK 315 cap j2EGens 32 && invsOK 315 j2E && memT 315 j2E j2TA &&
    j2EGens.all fun x => involOK 315 x && !tblEq 315 x j2TA

@[expose] def j2ENormalOK : Bool :=
  j2CG.all fun g => j2EGens.all fun e => memT 315 j2E (conjT 315 g (invT 315 g) e)

@[expose] def j2EStructOK : Bool :=
  j2E.all (fun x =>
    (tblEq 315 (compT 315 x x) (idT 315) || tblEq 315 (compT 315 x x) j2TA) &&
      j2E.all fun y => tblEq 315 (commutatorT 315 x y) (idT 315) ||
        tblEq 315 (commutatorT 315 x y) j2TA) &&
    j2E.all (fun x => !(j2E.all fun y => commTT 315 x y) || tblEq 315 x (idT 315) ||
      tblEq 315 x j2TA) &&
    j2E.all (fun y => commTT 315 j2TA y) &&
    (j2E.filter (involOK 315)).size == 11

@[expose] def j2ECentOK : Bool :=
  j2C2A.all fun g => !(j2EGens.all fun e => commTT 315 g e) || tblEq 315 g (idT 315) ||
    tblEq 315 g j2TA

@[expose] def j2Orb1Conj : List (List Nat) :=
  [[], [3], [7], [0, 3], [1, 3], [3, 3], [1, 7], [7, 7], [2, 1, 3], [3, 3, 3]]

@[expose] def j2Orb1Root : List Nat := [2, 2, 2]

@[expose] def j2Orb2Conj : List (List Nat) :=
  [[], [0], [1], [2], [3], [6], [1, 0], [2, 0], [3, 0], [6, 0], [2, 1], [3, 1], [7, 1], [0, 2],
    [0, 3], [1, 3], [3, 1, 0], [7, 1, 0], [0, 3, 0], [1, 3, 0]]

@[expose] def j2Orb2Root : List Nat := [2, 1, 6, 0]

@[expose] def conjOrbit (root : List Nat) (cs : List (List Nat)) : List Table :=
  cs.map fun w =>
    let c := evalWord 315 j2CG w
    conjT 315 c (invT 315 c) (evalWord 315 j2CG root)

@[expose] def j2OrbitOK : Bool :=
  enumOK 315 cap (j2TA :: conjOrbit j2Orb1Root j2Orb1Conj) 32 &&
    enumOK 315 cap (j2TA :: conjOrbit j2Orb2Root j2Orb2Conj) 32 &&
    j2E.all fun y => tblEq 315 y (idT 315) || tblEq 315 y j2TA ||
      memT 315 (conjOrbit j2Orb1Root j2Orb1Conj).toArray y ||
      memT 315 (conjOrbit j2Orb2Root j2Orb2Conj).toArray y

@[expose] def j2PerfPairs : List (List Nat × List Nat) :=
  [([2, 1, 7], [6, 1, 7]), ([7, 6, 6], [2, 2, 1]), ([3, 0], [3, 0, 7])]

@[expose] def j2PerfComm : List Table :=
  j2PerfPairs.map fun p => commutatorT 315 (evalWord 315 j2CG p.1) (evalWord 315 j2CG p.2)

@[expose] def j2PerfectOK : Bool := enumOK 315 cap j2PerfComm 1920

@[expose] def j2S1Gens : List Table := j2EGens ++ [j2CG[0]!, j2CG[1]!]

@[expose] def j2S2Gens : List Table :=
  j2S1Gens.map fun s => conjT 315 j2CG[3]! (invT 315 j2CG[3]!) s

@[expose] def j2SylowOK : Bool :=
  enumOK 315 cap j2S1Gens 128 && enumOK 315 cap j2S2Gens 128 &&
    (closArr 315 cap j2S1Gens).all fun x =>
      !memT 315 (closArr 315 cap j2S2Gens) x || memT 315 j2E x

@[expose] def j2NCInvs : Array Table := j2E.filter fun x => involOK 315 x && !tblEq 315 x j2TA

@[expose] def quadIdx (k : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range k).flatMap fun a => (List.range k).flatMap fun b => (List.range k).flatMap fun c =>
    (List.range k).map fun d => (a, b, c, d)

@[expose] def autPatOK (t : Nat × Nat × Nat × Nat) : Bool :=
  let a := j2NCInvs[t.1]!
  let b := j2NCInvs[t.2.1]!
  let c := j2NCInvs[t.2.2.1]!
  let d := j2NCInvs[t.2.2.2]!
  let e := j2EGens.toArray
  (commTT 315 a b == commTT 315 e[0]! e[1]!) && (commTT 315 a c == commTT 315 e[0]! e[2]!) &&
    (commTT 315 a d == commTT 315 e[0]! e[3]!) && (commTT 315 b c == commTT 315 e[1]! e[2]!) &&
    (commTT 315 b d == commTT 315 e[1]! e[3]!) && (commTT 315 c d == commTT 315 e[2]! e[3]!)

@[expose] def j2AutCount : Nat :=
  ((quadIdx j2NCInvs.size).filter autPatOK).length

end CFSG.GH74.Generic.S45.EvSpor
