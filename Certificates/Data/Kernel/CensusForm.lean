module

public import Certificates.Data.Kernel.XorSpan
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs

public section

namespace CFSG.KC.CensusForm

open CFSG.KC.Enum CFSG.KC.XorSpan CFSG.ComponentClassification.AS81.Census

@[expose] noncomputable def img (TL TH v : Nat) : Nat :=
  img2 (nat_lit 12) (nat_lit 4095) (nat_lit 6) (nat_lit 63) TL TH v

@[expose] noncomputable def xsK (F : Nat → Nat) (s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.xor acc (nIf(Nat.beq fld(s, b, nat_lit 1) (nat_lit 1), F b, nat_lit 0))) n

@[expose] noncomputable def tabK (M : Array Nat) (BL TL TH : Nat) : Bool :=
  bAnd(allN (nat_lit 12) (fun b =>
      Nat.beq fld(BL, Nat.mul (nat_lit 12) b, nat_lit 4095)
        (applyC M (Nat.shiftLeft (nat_lit 1) b))),
    allN (nat_lit 64) fun s =>
      bAnd(Nat.beq fld(TL, Nat.mul (nat_lit 12) s, nat_lit 4095)
          (xsK (fun b => fld(BL, Nat.mul (nat_lit 12) b, nat_lit 4095)) s (nat_lit 6)),
        Nat.beq fld(TH, Nat.mul (nat_lit 12) s, nat_lit 4095)
          (xsK (fun b => fld(BL, Nat.mul (nat_lit 12) (Nat.add (nat_lit 6) b), nat_lit 4095)) s
            (nat_lit 6))))

@[expose] noncomputable def qtK (QT : Nat) : Bool :=
  allN (nat_lit 4096) fun n =>
    Nat.beq fld(QT, Nat.mul (nat_lit 2) n, nat_lit 3) (qF (decodeV n)).code.val

@[expose] noncomputable def isomK (QT TL TH : Nat) : Bool :=
  allN (nat_lit 4096) fun n => strictB (img TL TH n) fun y =>
    bAnd(Nat.beq fld(QT, Nat.mul (nat_lit 2) y, nat_lit 3)
        fld(QT, Nat.mul (nat_lit 2) n, nat_lit 3),
      bIf(Nat.beq n (nat_lit 0), true, bIf(Nat.beq y (nat_lit 0), false, true)))

end CFSG.KC.CensusForm

end
