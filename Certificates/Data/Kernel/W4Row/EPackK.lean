module

public import Certificates.Data.Kernel.W4Row.E25K

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def e9PackK (n w idn X Y M1 M1I M2 M2I M3 M3I K KI : Nat) : Bool :=
  let b := pcomp n w (mask w) X (pcomp n w (mask w) (pcomp n w (mask w) K X) KI)
  Nat.beq (ppow n w (mask w) idn X 3) idn && Nat.beq (ppow n w (mask w) idn Y 3) idn &&
    !Nat.beq X idn && Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X) &&
    allN 3 (fun j => !Nat.beq Y (ppow n w (mask w) idn X j)) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M1 X) M1I) Y &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M2 X) M2I) (pcomp n w (mask w) X Y) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M3 X) M3I)
      (pcomp n w (mask w) X (ppow n w (mask w) idn Y 2)) &&
    Nat.beq (ppow n w (mask w) idn b 5) idn && !Nat.beq b idn

@[expose] noncomputable def e25PackK (n w idn X Y M1 M1I M2 M2I M3 M3I M4 M4I M5 M5I : Nat) :
    Bool :=
  Nat.beq (ppow n w (mask w) idn X 5) idn && Nat.beq (ppow n w (mask w) idn Y 5) idn &&
    !Nat.beq X idn && Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X) &&
    allN 5 (fun j => !Nat.beq Y (ppow n w (mask w) idn X j)) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M1 X) M1I) Y &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M2 X) M2I) (pcomp n w (mask w) X Y) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M3 X) M3I)
      (pcomp n w (mask w) X (ppow n w (mask w) idn Y 2)) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M4 X) M4I)
      (pcomp n w (mask w) X (ppow n w (mask w) idn Y 3)) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) M5 X) M5I)
      (pcomp n w (mask w) X (ppow n w (mask w) idn Y 4))

@[expose] noncomputable def conjInvsK (n w : Nat) (TS : List Nat) (HS : List (Nat × Nat))
    (X XI : Nat) : Bool :=
  Nat.beq TS.length HS.length &&
    (TS.zip HS).all fun q => conjInvK n w q.1 q.1 q.2.1 q.2.2 X XI

@[expose] noncomputable def e9FullK (n w : Nat) (G GI TS : List Nat)
    (wx wy wm1 wm2 wm3 wk : List Int) (whs : List (List Int)) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(gensTc n w TS TS,
    wordP n w (pidn n w) G GI wx fun X XI => wordP n w (pidn n w) G GI wy fun Y _ =>
    wordP n w (pidn n w) G GI wm1 fun M1 M1I => wordP n w (pidn n w) G GI wm2 fun M2 M2I =>
    wordP n w (pidn n w) G GI wm3 fun M3 M3I => wordP n w (pidn n w) G GI wk fun K KI =>
    wordsP n w (pidn n w) G GI whs fun HS =>
      e9PackK n w (pidn n w) X Y M1 M1I M2 M2I M3 M3I K KI && conjInvsK n w TS HS X XI)))

end CFSG.KC.W4E

end
