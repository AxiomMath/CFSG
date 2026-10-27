module

public import Certificates.Data.Kernel.Q8WitP

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum (pcomp pidn pg strictB)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def sqsK (n w N : Nat) (T SQ : Nat → Nat) : Bool :=
  allN N fun i => Nat.beq (SQ i) (pcomp n w (mask w) (T i) (T i))

@[expose] noncomputable def commTabK (n w N nc nm : Nat) (SQ C MK MZ : Nat → Nat) : Bool :=
  allN nm fun m => Nat.blt (MK m) nc && Nat.blt (MZ m) N && commK n w (C (MK m)) (SQ (MZ m))

@[expose] noncomputable def wit4RK (n w x y s c ci f P N : Nat) : Bool :=
  (bif Nat.beq f 1 then outsidePK n w x y s c x P else outsidePK n w x y s c y P) &&
    (Nat.blt (Nat.mod N 8192) n &&
      (bif Nat.beq (Nat.div N 8192) 0 then ncPK w x x c ci (Nat.mod N 8192) else
       bif Nat.beq (Nat.div N 8192) 1 then ncPK w x y c ci (Nat.mod N 8192) else
       bif Nat.beq (Nat.div N 8192) 2 then ncPK w y x c ci (Nat.mod N 8192) else
       ncPK w y y c ci (Nat.mod N 8192)))

@[expose] noncomputable def pairP2 (n w x y s nm : Nat) (SQ C CI MK MZ RM RF RO RN : Nat → Nat)
    (v : Nat) : Bool :=
  bif Nat.ble v 8192 then
    (Nat.blt 0 v && Nat.blt (Nat.sub v 1) n &&
      !Nat.beq (pg w (mask w) x (pg w (mask w) y (pg w (mask w) x (Nat.sub v 1))))
        (pg w (mask w) y (Nat.sub v 1)))
  else
    (Nat.blt (RM (Nat.sub v 8193)) nm && Nat.beq (SQ (MZ (RM (Nat.sub v 8193)))) s &&
      wit4RK n w x y s (C (MK (RM (Nat.sub v 8193)))) (CI (MK (RM (Nat.sub v 8193))))
        (RF (Nat.sub v 8193)) (RO (Nat.sub v 8193)) (RN (Nat.sub v 8193)))

@[expose] noncomputable def sq4K (n w s d : Nat) : Bool :=
  Nat.blt 0 d && Nat.blt (Nat.sub d 1) n &&
    !Nat.beq (pg w (mask w) s (pg w (mask w) s (Nat.sub d 1))) (Nat.sub d 1)

@[expose] noncomputable def q8WitFreeP2 (n w N ID : Nat) (T SQ D : Nat → Nat) (nm : Nat)
    (C CI MK MZ R RM RF RO RN : Nat → Nat) : Bool :=
  allN N fun i => strictB (SQ i) fun s =>
    Nat.beq s ID || sq4K n w s (D i) ||
      strictB (T i) fun x => strictB (R i) fun row =>
        allN N fun j =>
          !Nat.beq (SQ j) s ||
            pairP2 n w x (T j) s nm SQ C CI MK MZ RM RF RO RN (fldK 14 row j)

end CFSG.KC.Q8Wit

end
