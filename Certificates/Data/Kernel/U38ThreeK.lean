module

public import Certificates.Data.Kernel.U38FixK
public import Certificates.Data.Kernel.B3S3K

public section

namespace CFSG.KC.U38ThreeK

open CFSG.KC.Enum CFSG.KS CFSG.KC.U38QK CFSG.KC.U38FixK

@[expose] noncomputable def cubeIdxK (n w N : Nat) (T : Nat → Nat) : List Nat :=
  (List.range N).filter fun j => cubeK n w (T j)

@[expose] noncomputable def hElemL (n w : Nat) (T : Nat → Nat) (d e : Nat) (cs : List Nat) : Bool :=
  cs.all fun i => Nat.beq (T i) (pidn n w) || Nat.beq (T i) d || Nat.beq (T i) e ||
    (commK n w (T i) d && decide ((cs.filter fun j => commK n w (T i) (T j)).length ≤ 9))

@[expose] noncomputable def hElemK (n w N : Nat) (T : Nat → Nat) (d e : Nat) : Bool :=
  hElemL n w T d e (cubeIdxK n w N T)

@[expose] noncomputable def repOK (n w m NP : Nat) (P : Nat → Nat) (r N ng : Nat) (G : Nat → Nat) :
    Bool :=
  Nat.blt r NP && Nat.beq N NP && Nat.beq ng m &&
    allN m (fun j => Nat.beq (G j) (CFSG.KC.B3S3K.cj n w (P j) (P r)))

@[expose] noncomputable def coverK (n w NP nr : Nat) (P R : Nat → Nat) (i h : Nat) : Bool :=
  Nat.beq (P i) (pidn n w) || (Nat.blt h NP &&
    !(allN nr fun t => !Nat.beq (CFSG.KC.B3S3K.cj n w (P h) (P i)) (P (R t))))

@[expose] noncomputable def cjInv (n w p q : Nat) : Nat :=
  CFSG.KC.B3S3K.cm n w (pinvS n w (mask w) p) (CFSG.KC.B3S3K.cm n w q p)

end CFSG.KC.U38ThreeK

end
