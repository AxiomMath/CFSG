module

public import Certificates.Data.Kernel.Q8Wit

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum (pcomp pidn pg)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def fldK (b r j : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.mul b j)) (Nat.sub (Nat.shiftLeft 1 b) 1)

@[expose] noncomputable def q8AtK (w x y s j p : Nat) : Nat :=
  bif Nat.beq j 0 then p else
  bif Nat.beq j 1 then pg w (mask w) x p else
  bif Nat.beq j 2 then pg w (mask w) s p else
  bif Nat.beq j 3 then pg w (mask w) s (pg w (mask w) x p) else
  bif Nat.beq j 4 then pg w (mask w) y p else
  bif Nat.beq j 5 then pg w (mask w) y (pg w (mask w) x p) else
  bif Nat.beq j 6 then pg w (mask w) y (pg w (mask w) s p) else
  pg w (mask w) y (pg w (mask w) s (pg w (mask w) x p))

@[expose] noncomputable def outsidePK (n w x y s c a P : Nat) : Bool :=
  allN 8 fun j => Nat.blt (fldK 13 P j) n &&
    !Nat.beq (pg w (mask w) c (pg w (mask w) a (fldK 13 P j)))
      (q8AtK w x y s j (pg w (mask w) c (fldK 13 P j)))

@[expose] noncomputable def ncPK (w a u c ci p : Nat) : Bool :=
  !Nat.beq (pg w (mask w) a (pg w (mask w) c (pg w (mask w) u (pg w (mask w) ci p))))
    (pg w (mask w) c (pg w (mask w) u (pg w (mask w) ci (pg w (mask w) a p))))

@[expose] noncomputable def wit4PK (n w x y s c ci f P N : Nat) : Bool :=
  commK n w c s &&
    (bif Nat.beq f 1 then outsidePK n w x y s c x P else outsidePK n w x y s c y P) &&
    (Nat.blt (Nat.mod N 8192) n &&
      (bif Nat.beq (Nat.div N 8192) 0 then ncPK w x x c ci (Nat.mod N 8192) else
       bif Nat.beq (Nat.div N 8192) 1 then ncPK w x y c ci (Nat.mod N 8192) else
       bif Nat.beq (Nat.div N 8192) 2 then ncPK w y x c ci (Nat.mod N 8192) else
       ncPK w y y c ci (Nat.mod N 8192)))

end CFSG.KC.Q8Wit

end
