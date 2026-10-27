module

public import Certificates.Data.Kernel.YoshQ.TabN
public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH

@[expose] noncomputable def fldN (X b i : Nat) : Nat := (X >>> (b * i)) % 2 ^ b

@[expose] noncomputable def rpar (PL i : Nat) : Nat := fldN PL 16 (2 * i)

@[expose] noncomputable def rlab (PL i : Nat) : Nat := fldN PL 16 (2 * i + 1)

@[expose] noncomputable def lexB (a b c d : Nat) : Bool := Nat.blt a c || (Nat.beq a c && Nat.blt b d)

@[expose] noncomputable def treeAt (n w : Nat) (GS : List Nat) (EP PL i : Nat) : Bool :=
  Nat.blt (rpar PL i) i && Nat.blt (rlab PL i) GS.length &&
    eqN n w (fldN EP (n * w) i)
      (pmN n w (fldN EP (n * w) (rpar PL i)) (GS.getD (rlab PL i) 0))

@[expose] noncomputable def closeAt (n w cnt : Nat) (GS : List Nat) (EP PL POS h j : Nat) : Bool :=
  Nat.blt (fldN POS 16 (h * GS.length + j)) cnt &&
    eqN n w (pmN n w (fldN EP (n * w) h) (GS.getD j 0))
      (fldN EP (n * w) (fldN POS 16 (h * GS.length + j))) &&
    (Nat.beq (fldN POS 16 (h * GS.length + j)) 0 ||
      !lexB h j (rpar PL (fldN POS 16 (h * GS.length + j)))
        (rlab PL (fldN POS 16 (h * GS.length + j))))

@[expose] def incrL : List Nat → Bool
  | a :: b :: l => Nat.blt a b && incrL (b :: l)
  | _ => true

@[expose] noncomputable def sortedK (key : Nat → Nat) (cnt : Nat) (S : List Nat) : Bool :=
  Nat.beq S.length cnt && S.all (fun s => Nat.blt s cnt) && incrL (S.map key)

@[expose] noncomputable def replayK (n w m cap : Nat) (GS : List Nat) (cnt EP PL POS : Nat)
    (SM SF : List Nat) : Bool :=
  Nat.blt 0 cnt && Nat.ble cnt cap && eqN n w (fldN EP (n * w) 0) (pidn n w) &&
    Nat.beq (rpar PL 0) 0 && Nat.beq (rlab PL 0) 0 &&
    allN cnt (fun i => Nat.beq i 0 || treeAt n w GS EP PL i) &&
    allN cnt (fun i => Nat.beq i 0 || !Nat.blt (i + 1) cnt ||
      lexB (rpar PL i) (rlab PL i) (rpar PL (i + 1)) (rlab PL (i + 1))) &&
    allN cnt (fun h => allN GS.length (fun j => closeAt n w cnt GS EP PL POS h j)) &&
    sortedK (fun i => hkeyK m w (mask w) (fldN EP (n * w) i)) cnt SM &&
    sortedK (fun i => hkeyK n w (mask w) (fldN EP (n * w) i)) cnt SF

end CFSG.KC.YoshQ

end
