module

public import Certificates.Data.Kernel.W4Row.E25K

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def prK (n w idn Y W : Nat) (ab : Nat × Nat) : Nat :=
  pcomp n w (mask w) (ppow n w (mask w) idn Y ab.1) (ppow n w (mask w) idn W ab.2)

@[expose] noncomputable def invPackK (n w idn p m T TI Y YI W WI H HI : Nat)
    (cs : List (Nat × Nat)) : Bool :=
  Nat.beq (ppow n w (mask w) idn Y p) idn && Nat.beq (ppow n w (mask w) idn W p) idn &&
    Nat.beq (pcomp n w (mask w) Y W) (pcomp n w (mask w) W Y) &&
    !Nat.beq Y idn && allN p (fun k => !Nat.beq W (ppow n w (mask w) idn Y k)) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) T Y) TI) YI &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) T W) TI) WI &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) H Y) HI) (prK n w idn Y W (cs.getD 0 (0, 0))) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) H W) HI) (prK n w idn Y W (cs.getD 1 (0, 0))) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) HI Y) H) (prK n w idn Y W (cs.getD 2 (0, 0))) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) HI W) H) (prK n w idn Y W (cs.getD 3 (0, 0))) &&
    allN p (fun a => allN p (fun b => (a == 0 && b == 0) ||
      allN m (fun k => k == 0 ||
        allN p (fun j => !Nat.beq
          (pcomp n w (mask w) (pcomp n w (mask w) (ppow n w (mask w) idn H k)
            (prK n w idn Y W (a, b))) (ppow n w (mask w) idn HI k))
          (ppow n w (mask w) idn (prK n w idn Y W (a, b)) j)))))

@[expose] noncomputable def invFullK (n w p m : Nat) (G GI : List Nat) (T TI : Nat)
    (wy ww wh : List Int) (cs : List (Nat × Nat)) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI,
    wordP n w (pidn n w) G GI wy fun Y YI => wordP n w (pidn n w) G GI ww fun W WI =>
    wordP n w (pidn n w) G GI wh fun H HI =>
      invPackK n w (pidn n w) p m T TI Y YI W WI H HI cs))

end CFSG.KC.W4E

end
