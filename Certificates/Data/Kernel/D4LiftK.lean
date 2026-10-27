module

public import Certificates.Data.Kernel.D4K

public section

namespace CFSG.KC.D4Lift

open CFSG.KC.Enum (pg allN permOK)
open CFSG.KS (mask)
open CFSG.KC.D4K (siftOK)
open CFSG.KC.B3S3K (cm)

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN n (fun i => bIf(f i, false, true)), false, true)

@[expose] noncomputable def baseAll (w BP nb : Nat) (f : Nat → Bool) : Bool :=
  allN nb (fun t => f (pg w (mask w) BP t))

@[expose] noncomputable def baseAny (w BP nb : Nat) (f : Nat → Bool) : Bool :=
  anyN nb (fun t => f (pg w (mask w) BP t))

@[expose] noncomputable def invAt (w BP nb T : Nat) : Bool :=
  bAnd(baseAll w BP nb (fun b => Nat.beq (pg w (mask w) T (pg w (mask w) T b)) b),
    baseAny w BP nb (fun b => bIf(Nat.beq (pg w (mask w) T b) b, false, true)))

@[expose] noncomputable def commAt (w BP nb Z T : Nat) : Bool :=
  baseAll w BP nb (fun b => Nat.beq (pg w (mask w) Z (pg w (mask w) T b))
    (pg w (mask w) T (pg w (mask w) Z b)))

@[expose] noncomputable def cubeMoves (w BP nb Z : Nat) : Bool :=
  baseAny w BP nb (fun b =>
    bIf(Nat.beq (pg w (mask w) Z (pg w (mask w) Z (pg w (mask w) Z b))) b, false, true))

@[expose] noncomputable def pointK (w BP nb NQ : Nat) (QT : Nat → Nat) (NI : Nat) (IT : Nat → Nat)
    (Z : Nat) : Bool :=
  bIf(anyN NQ (fun j => Nat.beq Z (QT j)), true,
    bIf(cubeMoves w BP nb Z, true, anyN NI (fun j => commAt w BP nb Z (IT j))))

@[expose] noncomputable def liftK (n w : Nat) (LR TRI : Nat → Nat) (BP nb F0 PH NQ : Nat)
    (QT : Nat → Nat) (NI : Nat) (IT : Nat → Nat) (N : Nat) (T : Nat → Nat) : Bool :=
  bAnd(permOK n w (mask w) (Nat.mul n w) F0 (cm n w F0 F0),
    bAnd(siftOK n w LR TRI BP nb (cm n w F0 (cm n w PH PH)),
      bAnd(allN NI (fun j => bAnd(permOK n w (mask w) (Nat.mul n w) (IT j) (IT j),
          bAnd(siftOK n w LR TRI BP nb (IT j), invAt w BP nb (IT j)))),
        allN N (fun i => pointK w BP nb NQ QT NI IT (T i)))))

end CFSG.KC.D4Lift

end
