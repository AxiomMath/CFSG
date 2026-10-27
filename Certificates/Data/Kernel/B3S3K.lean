module

public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.LocalQT.Perm
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.B3S3K

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def cm (n w p q : Nat) : Nat := pcomp n w (mask w) p q

@[expose] noncomputable def pw (n w p e : Nat) : Nat := ppow n w (mask w) (pidn n w) p e

@[expose] noncomputable def cj (n w p q : Nat) : Nat :=
  cm n w p (cm n w q (pinvS n w (mask w) p))

@[expose] noncomputable def linesK (n w p N r : Nat) (T LX : Nat → Nat) : Bool :=
  allN N (fun k => !(Nat.beq (pw n w (T k) p) (pidn n w)) || Nat.beq (T k) (pidn n w) ||
      CFSG.KC.LQT.P.anyN r fun j => CFSG.KC.LQT.P.anyN p fun e =>
        Nat.beq (T k) (pw n w (LX j) e)) &&
    allN r (fun j => permB n w (LX j) && Nat.beq (pw n w (LX j) p) (pidn n w))

@[expose] noncomputable def transK (n w r : Nat) (H X L : Nat → Nat) (rec : List Nat) : Bool :=
  allN r fun j => permB n w (H j) && Nat.beq (cj n w (H j) (X (rec.getD j 0))) (L j)

@[expose] noncomputable def relsK (n w p BP X nb : Nat) (rels : List (Nat × Nat × Nat)) : Bool :=
  rels.all fun r => Nat.blt r.2.2 p && Nat.blt r.1 nb && Nat.blt r.2.1 nb &&
    Nat.beq (pg w (mask w) (pw n w X r.2.2) (pg w (mask w) BP r.1)) (pg w (mask w) BP r.2.1)

@[expose] noncomputable def commK (n w ng X : Nat) (G : Nat → Nat) : Bool :=
  allN ng fun k => permB n w (G k) && Nat.beq (cm n w (G k) X) (cm n w X (G k))

@[expose] noncomputable def zOK (n w z : Nat) : Bool :=
  !(Nat.beq z (pidn n w)) && Nat.beq (pw n w z 3) (pidn n w)

@[expose] noncomputable def convAt (n w N : Nat) (T : Nat → Nat) (qs rs : List Nat)
    (WJ WR : Nat → Nat) (i : Nat) : Bool :=
  !(qs.any fun q => Nat.beq (pw n w (T i) q) (pidn n w)) || Nat.beq (T i) (pidn n w) ||
    (Nat.blt (WJ i) N && rs.any (Nat.beq (WR i)) &&
      zOK n w (pw n w (cm n w (T i) (cj n w (T (WJ i)) (T i))) (WR i)))

end CFSG.KC.B3S3K

end
