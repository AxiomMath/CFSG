module

public import Certificates.Data.Kernel.M24L2.Letters
public import Certificates.Data.Kernel.M24L2.Bfs
public import CFSG.CGT.L5R.R3Inputs
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.M24L2

open CFSG.CGT.L5R.R3 CFSG.CGT.M24R CFSG.KC.Enum

@[expose] noncomputable def tEqK (w w' : N0Word) : Bool := Nat.beq (cwK w) (cwK w')

@[expose] noncomputable def identCheckK : Bool :=
  tEqK (thExp uD) (dExp uD) && tEqK (nW ++ dExp uD ++ inv10 nW) bW && tEqK (dExp bD) bW &&
    tEqK (thExp bD) dAW && !tEqK dAW [] &&
    (List.finRange 2).all fun j =>
      tEqK (dExp (yD j)) (yW j) && tEqK (inv10 nW ++ thExp (yD j) ++ nW) (dExp (a1D j)) &&
        tEqK (nW ++ thExp (a1D j) ++ inv10 nW) (dExp (b1D j)) && tEqK (thExp (b1D j)) (fW j) &&
        tEqK (inv10 wW ++ yW j ++ wW) (fW j)

@[expose] noncomputable def centLin (y1 y2 m : Nat) : Bool :=
  commK (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight y1 (nat_lit 4))) &&
    commK (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight y2 (nat_lit 4)))

@[expose] noncomputable def centBody (y1 y2 c : Nat) : Bool :=
  bIf(commK c y1 && commK c y2, Nat.beq c idC, true)

@[expose] noncomputable def centM (y1 y2 m : Nat) : Bool :=
  bIf(centLin y1 y2 m,
    allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c => centBody y1 y2 c, true)

@[expose] noncomputable def centE (E : List (Nat × Nat × Nat)) : Bool :=
  letN (cwK (yW 0)) fun y1 => letN (cwK (yW 1)) fun y2 =>
    centM y1 y2 (nat_lit 33825) && allL (fun e => letN e.1 fun m => centM y1 y2 m) E

end CFSG.KC.M24L2
