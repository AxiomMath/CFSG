module

public import Certificates.Data.Kernel.SmithD6.RepsK
public import Certificates.Data.Kernel.SmithD6.StabK
public import Certificates.Data.Kernel.SmithD6.E4f7Data

public section

namespace CFSG.KD.SmithD6E4

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Reps

@[expose] def e4Keys : List Nat := [16392, 65824, 16928, 4196608]

@[expose] def e4Pos : List Nat := [1579, 7907, 1663, 234203]

@[expose] def e4Out : Nat := 0x7DD7D77D

@[expose] def e4Cols (g : Nat) : Array Nat := tvColsP (pairK (e4Keys.getD g 0))

@[expose] def e4Ap : List Nat → Nat → Nat
  | [], c => c
  | g :: w, c => mf7Ap (e4Cols g) (e4Ap w c)

@[expose] noncomputable def e4GenOK (g : Nat) : Bool :=
  KT.find (e4Keys.getD g 0) lineTree == e4Pos.getD g 0 + 1 && commL (tvColsP (1, 2)) (e4Cols g)

@[expose] def e4BasisOK : Bool :=
  (List.range 32).all fun m => (mf7Ap (tvColsP (1, 2)) (2 ^ m) ^^^ 2 ^ m) &&& e4Out == 0

@[expose] def e4WordsOK (r : Nat) (W : List (Nat × List Nat)) : Bool :=
  W.all fun p => p.2.all (fun g => decide (g < 4)) && e4Ap p.2 r == p.1

@[expose] noncomputable def e4MemGo (x : Nat) (W : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => bIf(Nat.beq p.1 x, true, ih)) W

@[expose] noncomputable def e4ListGo (W : List (Nat × List Nat)) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => bAnd(bIf(Nat.beq (Nat.land x e4Out) 0, e4MemGo x W, true), ih)) l

@[expose] noncomputable def e4ChunksGo (cs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun ch _ ih => bAnd(e4ListGo JE.e4W ch, ih)) cs

@[expose] noncomputable def e4AllOK : Bool := e4ChunksGo J.wtC

@[expose] noncomputable def e4HeadOK : Bool :=
  (List.range 4).all e4GenOK && e4BasisOK && e4WordsOK (J.wtC.flatten.getD 1 0) JE.e4W

end CFSG.KD.SmithD6E4

end
