module

public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.D4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K

@[expose] noncomputable def siftOK (n w : Nat) (LR TRI : Nat → Nat) (BP nb G : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight G (n * w)) 0, bAnd(allN n (fun i => Nat.blt (pg w (mask w) G i) n),
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G))

@[expose] noncomputable def lineAt (n w p r : Nat) (T LX : Nat → Nat) (k : Nat) : Bool :=
  !(Nat.beq (pw n w (T k) p) (pidn n w)) || Nat.beq (T k) (pidn n w) ||
    CFSG.KC.LQT.P.anyN r fun j => CFSG.KC.LQT.P.anyN p fun e => Nat.beq (T k) (pw n w (LX j) e)

@[expose] noncomputable def imgBitsK (k w p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (2 ^ pg w (mask w) p i)) k

@[expose] noncomputable def permImgK (n w p : Nat) : Bool :=
  Nat.beq (Nat.shiftRight p (n * w)) 0 && allN n (fun i => Nat.blt (pg w (mask w) p i) n) &&
    Nat.beq (imgBitsK n w p) (2 ^ n - 1)

@[expose] noncomputable def transE (n w r : Nat) (H X L : Nat → Nat) (rec : List Nat) : Bool :=
  allN r fun j => permImgK n w (H j) &&
    eq22 n w (mask w) (H j) (X (rec.getD j 0)) (L j) (H j)

@[expose] noncomputable def cubeIdK (n w p : Nat) : Bool :=
  allN n fun i => Nat.beq (pg w (mask w) p (pg w (mask w) p (pg w (mask w) p i))) i

@[expose] noncomputable def lineCubeK (n w r : Nat) (T LX : Nat → Nat) (k : Nat) : Bool :=
  !(cubeIdK n w (T k)) || Nat.beq (T k) (pidn n w) ||
    CFSG.KC.LQT.P.anyN r fun j => Nat.beq (T k) (LX j) || eq2 n w (mask w) (T k) (LX j) (LX j)

end CFSG.KC.D4K

end
