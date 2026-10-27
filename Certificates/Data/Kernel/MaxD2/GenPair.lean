module

public meta import Certificates.Data.Kernel.MaxD2.Gen
public import Certificates.Data.Kernel.MaxD2.Gen

public section

namespace CFSG.KS.MaxD2.Gen

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

meta def pairList (nr : Nat) : List (Nat × Nat) :=
  (List.range nr).flatMap fun j => (List.range j).map fun i => (i, j)

meta def pairImgs (D : Data) (P : Pre) : Array Nat :=
  ((pairList P.rep.size).toArray.map fun (_, j) =>
    (D.fpPts.map fun b => P.rep[j]![b]!).toArray).flatten

meta def pairHints (D : Data) (w : Nat) (P : Pre) : Array Nat :=
  let ks := fpKeys P
  ((pairList P.rep.size).toArray.map fun (i, j) =>
    P.nT.map fun a => hint D w P ks P.rep[j]! P.repi[i]! a).flatten

end CFSG.KS.MaxD2.Gen

end
