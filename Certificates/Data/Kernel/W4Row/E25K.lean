module

public import Certificates.Data.Kernel.LocalQT.TcP
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def ep2LineK (n w idn X Y : Nat) : Nat → Nat
  | 0 => Y
  | i + 1 => pcomp n w (mask w) X (ppow n w (mask w) idn Y i)

@[expose] noncomputable def ep2BaseK (n w idn p X Y : Nat) : Bool :=
  Nat.beq (ppow n w (mask w) idn X p) idn && Nat.beq (ppow n w (mask w) idn Y p) idn &&
    !Nat.beq X idn && Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X) &&
    allN p (fun j => !Nat.beq Y (ppow n w (mask w) idn X j))

@[expose] noncomputable def ep2PartK (n w idn X Y : Nat) (idx : List (Nat × Nat × Nat))
    (MS : List (Nat × Nat)) : Bool :=
  Nat.beq idx.length MS.length && (idx.zip MS).all fun q =>
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) q.2.1 (ep2LineK n w idn X Y q.1.1)) q.2.2)
      (ppow n w (mask w) idn (ep2LineK n w idn X Y q.1.2.1) q.1.2.2)

@[expose] noncomputable def conjInvK (n w T TI H HI X XI : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) T
      (pcomp n w (mask w) (pcomp n w (mask w) H X) HI)) TI)
    (pcomp n w (mask w) (pcomp n w (mask w) H XI) HI)

@[expose] noncomputable def wordsP (n w idn : Nat) (G GI : List Nat) (ws : List (List Int))
    (k : List (Nat × Nat) → Bool) : Bool :=
  List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun wd _ ih k => wordP n w idn G GI wd fun A AI => ih fun L => k ((A, AI) :: L)) ws k

@[expose] noncomputable def ep2PackK (n w p : Nat) (G GI : List Nat) (TB TA : Nat)
    (idx : List (Nat × Nat × Nat)) (wx wy whb wha : List Int) (wms : List (List Int)) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(gensTc n w [TB, TA] [TB, TA],
    wordP n w (pidn n w) G GI wx fun X XI => wordP n w (pidn n w) G GI wy fun Y _ =>
    wordP n w (pidn n w) G GI whb fun B BI => wordP n w (pidn n w) G GI wha fun A AI =>
    wordsP n w (pidn n w) G GI wms fun MS =>
      ep2BaseK n w (pidn n w) p X Y && ep2PartK n w (pidn n w) X Y idx MS &&
        conjInvK n w TB TB B BI X XI && conjInvK n w TA TA A AI X XI)))

end CFSG.KC.W4E

end
