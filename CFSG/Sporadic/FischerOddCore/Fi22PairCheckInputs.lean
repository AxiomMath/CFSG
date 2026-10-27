module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheck
public import CFSG.Sporadic.FischerOddCore.Fi22QCheckInputs
public import Certificates.Data.CFSGNative.ONSchreier.Tools
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22QCheckInputs
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def fi22BadFix (f : Nat) : Bool := f == 54 || f == 182 || f == 72

@[expose] def fi22GoodFix (f : Nat) : Bool := f == 694 || f == 360 || f == 64

@[expose] def fi22H4Gens : Array (Array Nat) := Array.ofFn (n := 9) fun k => fi22QG 4 k.val

@[expose] def fi22PairAt (L : Array Level) (q qi v D pos ids lab : Array Nat)
    (gens : Array (Array Nat)) (I0 : Nat) (w h : Array Nat) : Bool :=
  let rw := resIdx 256 L q qi v D pos I0
  let fw := CFSG.ONSchreier.Native.fixCount 3510 w
  let hi := invCand 3510 h
  allLt 262144 fun I =>
    !(decide (lab[I]! < 79)) || I == I0 ||
      (let r := resIdx 256 L q qi v D pos I
      !(eqA 256 (compA 256 rw r) (compA 256 r rw)) ||
        (let x := resIdx 3510 L q qi v ids ids I
        let fx := CFSG.ONSchreier.Native.fixCount 3510 x
        let fp := CFSG.ONSchreier.Native.fixCount 3510 (compA 3510 w x)
        (fi22BadFix fx || fi22BadFix fp || (fx != fw && fp != fw && fx != fp)) &&
          (fw != 64 || fx != 694 || fi22BadFix fp ||
            (let y := conjArr 3510 h hi x
            allLt gens.size fun k =>
              eqA 3510 (compA 3510 gens[k]! y) (compA 3510 y gens[k]!)))))

@[expose] def fi22PairOK (L : Array Level) (q qi v D pos lab roots : Array Nat)
    (A : Nat → Array Nat) (gens : Array (Array Nat)) : Bool :=
  let ids := idA 3510
  allLt 79 fun j =>
    let I0 := roots[j]!
    let w := resIdx 3510 L q qi v ids ids I0
    !(fi22GoodFix (CFSG.ONSchreier.Native.fixCount 3510 w)) ||
      fi22PairAt L q qi v D pos ids lab gens I0 w (A (106 + j))

end CFSG.Sporadic.FischerOddCore
