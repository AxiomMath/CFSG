module

public import Certificates.Data.Kernel.FzUT.Norm3

public section

namespace CFSG.KC.FzZ8

open CFSG.KC.FzUT

@[expose] noncomputable def apZ (M p : Nat) : Nat :=
  Nat.add
    (Nat.mod (Nat.add (Nat.mul (fldN M 3 7 0) (Nat.land p 7))
      (Nat.mul (fldN M 3 7 1) (Nat.shiftRight p 3))) 8)
    (Nat.mul 8 (Nat.mod (Nat.add (Nat.mul (fldN M 3 7 2) (Nat.land p 7))
      (Nat.mul (fldN M 3 7 3) (Nat.shiftRight p 3))) 8))

@[expose] noncomputable def apCZ (b M q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) q (apZ M q) (Nat.beq b 1)

@[expose] noncomputable def actZ (T S L v q : Nat) : Nat :=
  apCZ (Nat.land v 1) T (apCZ (Nat.land (Nat.shiftRight v 1) 1) S
    (apCZ (Nat.land (Nat.shiftRight v 2) 1) L q))

@[expose] noncomputable def addZ (p q : Nat) : Nat :=
  Nat.add (Nat.land (Nat.add (Nat.land p 7) (Nat.land q 7)) 7)
    (Nat.mul 8 (Nat.land (Nat.add (Nat.shiftRight p 3) (Nat.shiftRight q 3)) 7))

@[expose] noncomputable def emZ (T S L x y : Nat) : Nat :=
  Nat.add (addZ (Nat.land x 63) (actZ T S L (Nat.shiftRight x 6) (Nat.land y 63)))
    (Nat.mul 64 (Nat.xor (Nat.shiftRight x 6) (Nat.shiftRight y 6)))

@[expose] noncomputable def tlZ (T x : Nat) : Bool :=
  band (Nat.beq (apZ T (Nat.land x 63)) (Nat.land x 63)) (Nat.beq (Nat.land (Nat.shiftRight x 6) 3) 0)

@[expose] noncomputable def wZ (T x : Nat) : Bool :=
  band (Nat.beq (apZ T (Nat.land x 63)) (Nat.land x 63)) (Nat.blt (Nat.shiftRight x 6) 2)

@[expose] noncomputable def tzZ (x : Nat) : Bool :=
  band (Nat.beq (Nat.shiftRight x 6) 1) (Nat.beq (Nat.land x 27) 0)

@[expose] noncomputable def rhZ (x : Nat) : Nat :=
  Nat.add (apZ 3704 (Nat.land x 63)) (Nat.mul 64 (Nat.shiftRight x 6))

end CFSG.KC.FzZ8
