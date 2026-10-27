module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMaxInputs

public section

namespace CFSG.Certificates.Kernel.PkCV.L34MaxT

open CFSG.GH74.KGroups.L34 CFSG.RankThree.PartTwo.KFacts.L34Max

@[expose] def orL (l : List Nat) : Nat := l.foldr (fun k s => s ||| (1 <<< k)) 0

@[expose] def u0L : List Nat := [2, 3, 4, 6, 7, 8, 9, 13, 17]

@[expose] noncomputable def keyN (y : CV 21) : Nat := orL (u0L.map (img 21 y.1))

@[expose] noncomputable def targetBits : Nat :=
  orL ((elemsC QN0).flatMap fun n => (reps.map cOf).map fun g => keyN (n * g))

@[expose] noncomputable def stabC : Bool :=
  let tb := targetBits
  (elemsC QP21).all fun y =>
    let k := keyN y
    if k = orL u0L then siftC QN0 y 0 else tb.testBit k

end CFSG.Certificates.Kernel.PkCV.L34MaxT

end
