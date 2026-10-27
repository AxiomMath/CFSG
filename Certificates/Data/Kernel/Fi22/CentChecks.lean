module

public import Certificates.Data.CFSGNative.Fi22.Centralizer
public import Certificates.Data.Kernel.Fi22.Cent

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F4.Native CFSG.KS.Fi22Cent

@[expose] def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => iterN f n (f x)

@[expose] def cPt (O : COrbit) (k x : Nat) : Nat := ap (cTab O (genTables O (-2)) k) x

@[expose] def cPowOK (O : COrbit) (w : List Nat) (m : Nat) : Bool :=
  chainQ.all fun q => iterN (ap (wordTab O (genTables O (-2)) w)) m q == ap O.alpha q

@[expose] noncomputable def centGenOK (O : COrbit) (e p : Array Nat) : Bool :=
  allIn 0 6 fun s => GSK s < 693 && allIn 0 693 fun j =>
    uPts[phiData[p[cPt O e[GSK s]! e[j]!]!]!]! ==
      normC (tvC uPts[phiData[GSK s]!]! uPts[phiData[j]!]!)

@[expose] noncomputable def centTreeOK (O : COrbit) (e p : Array Nat) : Bool :=
  ORK 0 == GSK 0 &&
    allIn 1 693 (fun t => TPK t < t && TGK t < 6 &&
      ORK t == p[cPt O e[GSK (TGK t)]! e[ORK (TPK t)]!]!) &&
    allIn 0 693 (fun i => OIK i < 693 && ORK (OIK i) == i)

@[expose] noncomputable def centChecksK (O : COrbit) : Bool :=
  let e := eaPts O
  let p := ePos e
  let L := chainLetters O
  e.size == 693 && phiData.size == 693 &&
    allIn 0 693 (fun i => phiData[i]! < 693 && phiPos[phiData[i]!]! == i) &&
    (levelLetters L chainBase 1).all (fun l =>
      allIn 0 693 (fun i => p[ap L[l]! e[i]!]! < 693) &&
        sift t46Trees t46Letters t46Base t46Q 0 (rrImg e p L[l]!)) &&
    centGenOK O e p && centTreeOK O e p &&
    aWord.all (fun k => e.contains k) && cPowOK O aWord 9 &&
    aWord2.all (fun k => e.contains k) && cPowOK O aWord2 11

end CFSG.Sporadic.Fi22.Native

end
