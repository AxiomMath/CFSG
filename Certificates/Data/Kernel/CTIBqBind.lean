module

public import Certificates.Data.Kernel.CTIBq
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.OddSquareCertInputs

public section

namespace CFSG.KC.CTIBq

open CFSG.KLie.CT CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Bin

@[expose] noncomputable def bindsL (GR : Nat) (gL : List Nat) (A6 : Nat) (a6 : List Nat) (A8 : Nat)
    (a8 : List Nat) (Q1 : Nat) (q1 : List Nat) (Q2 : Nat) (q2 : List Nat) : Bool :=
  andB (andB (Nat.beq (lenL gL) 22) (bindL GR 22 gL))
    (andB (andB (Nat.beq (lenL a6) 22) (bindL A6 23 a6))
    (andB (andB (Nat.beq (lenL a8) 22) (bindL A8 23 a8))
    (andB (andB (Nat.beq (lenL q1) 22) (bindL Q1 22 q1))
      (andB (Nat.beq (lenL q2) 22) (bindL Q2 22 q2)))))

@[expose] noncomputable def bindsK (GR A6 A8 Q1 Q2 : Nat) : Bool :=
  bindsL GR gramRows A6 liftImgs6 A8 liftImgs8 Q1 quotRows1 Q2 quotRows2

@[expose] def decL (c : Nat) : Int := if c = 0 then 1 else if c = 1 then 2 else -2

end CFSG.KC.CTIBq

end
