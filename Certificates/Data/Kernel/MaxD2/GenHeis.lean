module

public meta import Certificates.Data.Kernel.MaxD2.GenPair
public meta import Certificates.Data.MaxD2Heis
public import Certificates.Data.Kernel.MaxD2.GenPair

public section

namespace CFSG.KS.MaxD2.Gen

open CFSG.PSL3Four.Native Certificates.MaxD2Perm Certificates.MaxD2Heis

meta def hrTabs (D : Data) : Array Tab := (hrEnum D).tabs

meta def zPos (D : Data) : Array Nat :=
  let rT := hrTabs D
  let u := (rGens D)[0]!
  let v := (rGens D)[1]!
  ((List.range rT.size).filter fun r => commutesUV D.n u v rT[r]!).toArray

meta def zIdx (D : Data) : Array Nat :=
  let zp := zPos D
  (List.range (hrTabs D).size).toArray.map fun r =>
    ((List.range zp.size).find? fun j => zp[j]! == r).map (· + 1) |>.getD 0

meta def commHints (D : Data) : Array Nat :=
  let n := D.n
  let rT := hrTabs D
  let zT := (zPos D).map fun r => rT[r]!
  ((List.range rT.size).toArray.map fun k => (List.range rT.size).toArray.map fun l =>
    let xy := comp n rT[k]! rT[l]!
    let yx := comp n rT[l]! rT[k]!
    ((List.range zT.size).find? fun j => xy == comp n zT[j]! yx).getD 0).flatten

meta def pairsBy (mk cn : Array Nat) : Array (Nat × Nat) :=
  ((pairList mk.size).filter fun (i, j) => mk[i]! == mk[j]! && cn[i]! == cn[j]!).toArray

meta def pairPos (nr : Nat) (ps : Array (Nat × Nat)) : Array Nat :=
  (pairList nr).toArray.map fun ij => ((List.range ps.size).find? fun q => ps[q]! == ij).getD 0

meta def pairImgsL (D : Data) (P : Pre) (ps : Array (Nat × Nat)) : Array Nat :=
  (ps.map fun (_, j) => (D.fpPts.map fun b => P.rep[j]![b]!).toArray).flatten

meta def pairHintsL (D : Data) (w : Nat) (P : Pre) (ps : Array (Nat × Nat)) : Array Nat :=
  let ks := fpKeys P
  (ps.map fun (i, j) => P.nT.map fun a => hint D w P ks P.rep[j]! P.repi[i]! a).flatten

end CFSG.KS.MaxD2.Gen

end
