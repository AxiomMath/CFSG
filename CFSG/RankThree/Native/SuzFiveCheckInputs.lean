module

public import CFSG.RankThree.Native.SuzFiveDefs
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.RankThree.Native.SuzFiveDefs
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.Sporadic.SuzOddCore.SmallChainCheck
public meta import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public import Mathlib.GroupTheory.Schreier
public meta import Mathlib.GroupTheory.Schreier
public import Std.Data.HashMap

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore

@[expose] def suzFiveKeys : List Nat := [0, 1, 2, 3, 4, 8, 5, 6]

@[expose] def suzFiveInM (g : Array Nat) : Bool := siftA 1782 smallLevels smallBaseNat.toArray 0 g

@[expose] def suzFiveInT (g : Array Nat) : Bool := suzFiveInM g || suzFiveInM (compA 1782 vArr g)

@[expose] def suzFiveQCert : ArrCert := enumBfs 1782 suzFiveQArrs suzFiveKeys 30

@[expose] def suzFiveLines : Array (Array Nat) := Array.ofFn (n := 6) fun i => suzFiveLineArr i

@[expose] def suzFiveQCheck (c : ArrCert) (xs : Array (Array Nat)) : Bool :=
  enumOK 1782 suzFiveQArrs suzFiveKeys c && c.pts.size == 25 &&
    commA 1782 suzFiveQArrs[0]! suzFiveQArrs[1]! && suzFiveQArrs.size == 2 &&
    suzFiveInM suzFiveQArrs[0]! && suzFiveInM suzFiveQArrs[1]! &&
    allLt 25 (fun k => eqA 1782 (powArr 1782 c.pts[k]! 5) (idA 1782)) &&
    allLt 25 (fun k => eqA 1782 c.pts[k]! (idA 1782) ||
      (List.range 6).any fun j => (List.range 5).any fun e =>
        eqA 1782 c.pts[k]! (powArr 1782 xs[j]! e)) &&
    allLt 6 (fun j => allLt 6 fun j' => j == j' ||
      allLt 5 fun e => !(eqA 1782 xs[j]! (powArr 1782 xs[j']! e))) &&
    allLt 6 (fun j => validA 1782 xs[j]! && eqA 1782 (powArr 1782 xs[j]! 5) (idA 1782) &&
      !(eqA 1782 xs[j]! (idA 1782)) && c.pts.toList.any (eqA 1782 xs[j]!))

@[expose] def suzFiveCCert (i : Nat) : ArrCert := enumBfs 1782 (suzFiveCArrs i) suzFiveKeys 3700

@[expose] def suzFiveDCert (i : Nat) : ArrCert := enumBfs 1782 (suzFiveDArrs i) suzFiveKeys 400

@[expose] def suzFiveCCheck (cs : Array (Array Nat)) (x : Array Nat) (c : ArrCert) (sz : Nat) :
    Bool :=
  enumOK 1782 cs suzFiveKeys c && c.pts.size == sz &&
    allLt cs.size (fun k => commA 1782 cs[k]! x && suzFiveInT cs[k]!) &&
    validA 1782 x && c.pts.toList.any (eqA 1782 x)

@[expose] def suzFivePosKeys (m : Nat) : List Nat := List.range m

@[expose] def suzFiveOrbitCheck (ds : Array (Array Nat)) (L : List Nat) (m dsz : Nat)
    (c : ArrCert) : Bool :=
  L.length == m && ds.all (fun g => L.all fun x => L.contains g[x]!) &&
    enumOK m (ds.map (restrictArr L)) (suzFivePosKeys m) c && c.pts.size == dsz

@[expose] def suzFiveCentCount (c : ArrCert) (ds : Array (Array Nat)) : Nat :=
  ((List.range c.pts.size).filter fun k =>
    allLt ds.size fun l => commA 1782 c.pts[k]! ds[l]!).length

@[expose] def suzFiveDCheck (cs : Array (Array Nat)) (cC : ArrCert) (ds : Array (Array Nat))
    (cD : ArrCert) (dsz : Nat) (x : Array Nat) (cnt : Nat) : Bool :=
  enumOK 1782 ds suzFiveKeys cD && cD.pts.size == dsz && 2 ≤ ds.size &&
    allLt cs.size (fun k => allLt ds.size fun l =>
      cD.pts.toList.any (eqA 1782 (conjA 1782 cs[k]! ds[l]!))) &&
    allLt cs.size (fun k => allLt cs.size fun l =>
      cD.pts.toList.any (eqA 1782 (commutatorA 1782 cs[k]! cs[l]!))) &&
    allLt ds.size (fun l => suzFiveInM ds[l]!) &&
    !(commA 1782 ds[0]! ds[1]!) && suzFiveCentCount cC ds == cnt &&
    (cnt != 5 || allLt cC.pts.size (fun k =>
      !(allLt ds.size fun l => commA 1782 cC.pts[k]! ds[l]!) ||
        (List.range 5).any fun e => eqA 1782 cC.pts[k]! (powArr 1782 x e)))

@[expose] def suzFivePairsCheck (i : Nat) : Bool :=
  let E := suzFiveBfs i
  let c := suzFiveCCert i
  allLt suzFiveDerivedPairs[i]!.size fun l =>
    decide ((suzFiveDerivedPairs[i]!)[l]!.1 < (suzFiveCArrs i).size) &&
      validA 1782 E[(suzFiveDerivedPairs[i]!)[l]!.2]! &&
      c.pts.toList.any (eqA 1782 E[(suzFiveDerivedPairs[i]!)[l]!.2]!)

@[expose] def suzFiveOrbitCert (i : Nat) : ArrCert :=
  enumBfs suzFiveOrbits[i]!.length ((suzFiveDArrs i).map (restrictArr suzFiveOrbits[i]!))
    (suzFivePosKeys suzFiveOrbits[i]!.length) 400

@[expose] def suzFiveStage (t : Array Nat) (init : Nat) (steps : List (Nat × Nat × Nat)) :
    Nat → Array Nat
  | 0 => refineIterT t (initColour "fixed" t) init
  | s + 1 => refineIterT t (indivPoint (suzFiveStage t init steps s) (steps.getD s (0, 0, 0)).1 s)
      (steps.getD s (0, 0, 0)).2.2

@[expose] def suzFiveGraphCheck (t : Array Nat) (init : Nat) (steps : List (Nat × Nat × Nat)) :
    Bool :=
  steps.all (fun s => decide (s.1 < 1782)) &&
    allLt steps.length (fun s => decide (classCount (suzFiveStage t init steps s)
      (steps.getD s (0, 0, 0)).1 ≤ (steps.getD s (0, 0, 0)).2.1)) &&
    ((suzFiveStage t init steps steps.length).toList.take 1782).Nodup &&
    (suzFiveStage t init steps steps.length).size == 1782

end CFSG.RankThree.Native
