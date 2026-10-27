module

public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def fi22SylSeeds (s : Nat) : Array (Array Nat) :=
  (List.range (fi22CentSylowField s 4)).toArray.map fun i =>
    fi22CentArr (fi22CentSylowField s 3 + i)

@[expose] def fi22SylGens (s : Nat) : Array (Array Nat) :=
  fi22SylSeeds s ++ (fi22SylSeeds s).map (invCand 3510)

@[expose] def fi22SylWits (s : Nat) : Array (Array Nat) :=
  (List.range (fi22CentSylowField s 7)).toArray.map fun w =>
    fi22CentArr (fi22CentWitField (fi22CentSylowField s 6 + w) 0)

@[expose] def fi22SylOK (s : Nat) : Bool :=
  let c := fi22CentSylowField s 0
  let p := fi22CentSylowField s 1
  let G := fi22SylGens s
  let r := closureSearch 3510 G (fi22CentSylowField s 2 + 1)
  let E := r.1
  let base : Array Nat := #[0, 1, 2, 3, 6, 4]
  let Ls := rawLevels 3510 (fi22CentStrong c) base
  let xs := fi22SylWits s
  closureOK 3510 G E r.2.1 r.2.2.1 r.2.2.2 && E.size == fi22CentSylowField s 2 &&
    keysOK 3510 [0, 1, 2, 3, 6, 4] E &&
    allLt (fi22CentSylowField s 4) (fun i =>
      siftA 3510 Ls base 0 (fi22CentArr (fi22CentSylowField s 3 + i))) &&
    coverOK 3510 p E xs (coverSearch 3510 p E xs) &&
    allLt (fi22CentSylowField s 7) fun w =>
      let x := xs[w]!
      let h := fi22CentArr (fi22CentWitField (fi22CentSylowField s 6 + w) 1)
      let o := fi22CentWitField (fi22CentSylowField s 6 + w) 3
      let y := compA 3510 x (compA 3510 h (compA 3510 x (invCand 3510 h)))
      isOrdP 3510 p x && siftA 3510 Ls base 0 x && siftA 3510 Ls base 0 h && o % 2 == 0 &&
        eqA 3510 (Native.powA 3510 y o) (idA 3510) &&
          !(eqA 3510 (Native.powA 3510 y (o / 2)) (idA 3510))

end CFSG.Sporadic.FischerOddCore
