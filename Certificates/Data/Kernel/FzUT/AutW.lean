module

public import Certificates.Data.Kernel.FzUT.Shape
public import Certificates.Data.Kernel.FzUT.BU

public section

namespace CFSG.KC.FzUT

@[expose] noncomputable def atOK (T S L AT : Nat) : Bool :=
  allN 512 fun i => Nat.beq (fldN AT 6 63 i) (actP T S L (i >>> 6) (i &&& 63))

@[expose] noncomputable def emPT (AT x y : Nat) : Nat :=
  pmulP (x &&& 63) (fldN AT 6 63 (64 * (x >>> 6) + (y &&& 63))) + 64 * ((x >>> 6) ^^^ (y >>> 6))

@[expose] noncomputable def cmT (AT u w : Nat) : Bool := Nat.beq (emPT AT u w) (emPT AT w u)

@[expose] noncomputable def bN (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 b

@[expose] noncomputable def roA (RO c : Nat) : Nat := fldN RO 10 1023 c

@[expose] noncomputable def rfA (RO c : Nat) : Nat := Nat.sub (roA RO (Nat.succ c)) (roA RO c)

@[expose] noncomputable def rlA (RL j : Nat) : Nat := fldN RL 9 511 j

@[expose] noncomputable def ltA (LT c : Nat) : Nat := fldN LT 48 281474976710655 c

@[expose] noncomputable def rootsOK (AT RL RO : Nat) : Bool :=
  band (Nat.beq (roA RO 0) 0) (band (Nat.beq (roA RO 512) 512)
    (allN 512 fun c => band (Nat.ble (roA RO c) (roA RO (Nat.succ c)))
      (allN (rfA RO c) fun j => sb (rlA RL (roA RO c + j)) fun y =>
        band (Nat.beq (emPT AT y y) c)
          (bimp (Nat.blt (Nat.succ j) (rfA RO c)) (Nat.blt y (rlA RL (roA RO c + Nat.succ j)))))))

@[expose] noncomputable def lab0F (RO c q q2 : Nat) : Nat :=
  rfA RO c + 1024 * rfA RO q + 1048576 * rfA RO q2 + 1073741824 * bN (Nat.beq q 0) +
    2147483648 * bN (Nat.beq q2 0)

@[expose] noncomputable def lab0OK (AT RO LT : Nat) : Bool :=
  allN 512 fun c => sb (emPT AT c c) fun q => sb (emPT AT q q) fun q2 =>
    Nat.beq (ltA LT c) (lab0F RO c q q2)

@[expose] noncomputable def roundOK (AT LT LT' u n UL : Nat) : Bool :=
  band (Nat.beq (cntB 512 fun y => Nat.beq (ltA LT y) u) n)
    (band (allN n fun j => band (Nat.beq (ltA LT (rlA UL j)) u)
        (bimp (Nat.blt (Nat.succ j) n) (Nat.blt (rlA UL j) (rlA UL (Nat.succ j)))))
      (allN 512 fun c => Nat.beq (ltA LT' c)
        (16 * ltA LT c + cntB n fun j => cmT AT c (rlA UL j))))

@[expose] noncomputable def inWc (T c : Nat) : Bool :=
  band (Nat.beq (evD T (c &&& 63)) (c &&& 63)) (Nat.beq ((c >>> 6) &&& 6) 0)

@[expose] noncomputable def finalOK (T LT LW nw : Nat) : Bool :=
  allN 512 fun c => sb (ltA LT c) fun v =>
    Bool.rec (motive := fun _ => Bool) (bnot (anyN nw fun i => Nat.beq (ltA LW i) v))
      (anyN nw fun i => Nat.beq (ltA LW i) v) (inWc T c)

end CFSG.KC.FzUT
