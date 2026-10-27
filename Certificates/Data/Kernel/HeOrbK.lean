module

public import CFSG.Certificates.Kernel.Orders.Mat
public import Certificates.Data.Kernel.Spor.VOrb
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.SporSch.LyMat

public section

namespace CFSG.KC.HeOrb

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS.PEnum CFSG.KS.Row CFSG.KS.VO CFSG.KS.SporSch.LyM

@[expose] noncomputable def cL : Nat := rep1 (nat_lit 12) (nat_lit 2500)

@[expose] noncomputable def cH : Nat := Nat.shiftLeft cL (nat_lit 11)

@[expose] noncomputable def cCM : Nat := Nat.mul (nat_lit 4095) (rep1 (nat_lit 600) (nat_lit 50))

@[expose] noncomputable def cRM : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 600)) (nat_lit 1)

@[expose] noncomputable def cONE : Nat := rep1 (nat_lit 612) (nat_lit 50)

@[expose] noncomputable def cLV : Nat := rep1 (nat_lit 12) (nat_lit 50)

@[expose] noncomputable def cHV : Nat := Nat.shiftLeft cLV (nat_lit 11)

@[expose] noncomputable def mulH (X Y : Nat) : Nat :=
  mulR (nat_lit 7) (nat_lit 12) (nat_lit 600) (nat_lit 50) (nat_lit 8) cL cH cCM cRM X Y

@[expose] noncomputable def vldH (X : Nat) : Bool :=
  validM (nat_lit 7) (nat_lit 30000) cL cH X

@[expose] noncomputable def code (PT : Nat → Nat) (i : Nat) : Nat :=
  rg (nat_lit 600) cRM PT (nat_lit 0) i

@[expose] noncomputable def trK (M MT : Nat) : Bool :=
  allN (nat_lit 50) fun i => allN (nat_lit 50) fun j =>
    Nat.beq
      (Nat.land (Nat.shiftRight MT (Nat.add (Nat.mul (nat_lit 600) i) (Nat.mul (nat_lit 12) j)))
        (nat_lit 4095))
      (Nat.land (Nat.shiftRight M (Nat.add (Nat.mul (nat_lit 600) j) (Nat.mul (nat_lit 12) i)))
        (nat_lit 4095))

@[expose] noncomputable def matK (csA csB : List Char) (TA TB : Nat) : Bool :=
  bAnd(constsOK (nat_lit 7) (nat_lit 12) (nat_lit 600) (nat_lit 50) (nat_lit 8) cL cH cCM cRM cONE
      cLV cHV,
  bAnd(vldH TA, bAnd(vldH TB,
  bAnd(strictB (payRunP (nat_lit 7) (nat_lit 50) (nat_lit 12) (nat_lit 600) csA (nat_lit 0)
      (nat_lit 0) (nat_lit 0)) fun MA => trK MA TA,
    strictB (payRunP (nat_lit 7) (nat_lit 50) (nat_lit 12) (nat_lit 600) csB (nat_lit 0)
      (nat_lit 0) (nat_lit 0)) fun MB => trK MB TB))))

@[expose] noncomputable def rowF (Y r : Nat) : Nat :=
  Nat.land (Nat.shiftRight Y (Nat.mul (nat_lit 600) r)) cRM

@[expose] noncomputable def blkRow (PT AL BE : Nat → Nat) (YA YB i r : Nat) : Bool :=
  bIf(Nat.blt i (nat_lit 8330),
    bAnd(Nat.blt (r32 AL i) (nat_lit 8330), bAnd(Nat.blt (r32 BE i) (nat_lit 8330),
    bAnd(Nat.beq (rowF YA r) (code PT (r32 AL i)), Nat.beq (rowF YB r) (code PT (r32 BE i))))),
    true)

@[expose] noncomputable def blkK (PT AL BE : Nat → Nat) (TA TB s : Nat) : Bool :=
  strictB (PT s) fun X => bAnd(vldH X,
    strictB (mulH X TA) fun YA => strictB (mulH X TB) fun YB =>
      allN (nat_lit 32) fun r => blkRow PT AL BE YA YB (Nat.add (Nat.mul (nat_lit 32) s) r) r)

@[expose] noncomputable def hdK (PT AL BE PA LA : Nat → Nat) (R : List Nat) : Bool :=
  bAnd(Nat.beq (r32 PA (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (r32 LA (nat_lit 0)) (nat_lit 0),
  bAnd(Nat.beq (vorbCnt (nat_lit 8330) AL BE PA LA) (nat_lit 8330),
    strictB (code PT (nat_lit 0)) fun c => allN (nat_lit 50) fun j =>
      Nat.beq (Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 12) j)) (nat_lit 4095))
        (List.getD R j (nat_lit 0)))))

@[expose] noncomputable def srtK (PT SO : Nat → Nat) : Bool :=
  allN (nat_lit 8330) (vorbSortK (nat_lit 8330) (code PT) SO)

@[expose] noncomputable def tabK (AL : Nat → Nat) (w m P : Nat) : Bool :=
  allN (nat_lit 8330) fun x => Nat.beq (r32 AL x) (pg w m P x)

end CFSG.KC.HeOrb

end
