module

public import Certificates.Data.Kernel.LocalQT.TcP
public import Certificates.Data.Kernel.PkPow

public section

namespace CFSG.KC.B45P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.PkPow

@[expose] noncomputable def invProdP (n w idn : Nat) (G GI : List Nat) (T TI : Nat)
    (wd : List Int) (k : Nat → Nat → Bool) : Bool :=
  wordP n w idn G GI wd fun g gi =>
    strictB (pcomp n w (mask w) (pcomp n w (mask w) g T) gi) fun C =>
      strictB (pcomp n w (mask w) g (pcomp n w (mask w) TI gi)) fun CI =>
        strictB (pcomp n w (mask w) T C) fun Z =>
          strictB (pcomp n w (mask w) CI TI) fun ZI => k Z ZI

@[expose] noncomputable def ordK (n w p idn X : Nat) : Bool :=
  bAnd(Nat.beq (ppw n w X p) idn, bIf(Nat.beq X idn, false, true))

@[expose] noncomputable def cfgK (n w p idn Z X XI Y YI : Nat) : Bool :=
  bAnd(Nat.beq Z (pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) X Y) XI) YI),
    bAnd(Nat.beq (ppw n w X p) idn,
      bAnd(Nat.beq (pcomp n w (mask w) Z X) (pcomp n w (mask w) X Z),
        bAnd(Nat.beq (pcomp n w (mask w) Z Y) (pcomp n w (mask w) Y Z),
          bIf(Nat.beq Z idn, false, true)))))

@[expose] noncomputable def b45OrdK (n w p : Nat) (G GI : List Nat) (T TI : Nat)
    (wd : List Int) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(permOK n w (mask w) (n * w) T TI,
    strictB (pidn n w) fun idn =>
      invProdP n w idn G GI T TI wd fun Z _ => ordK n w p idn Z)))

@[expose] noncomputable def b45CfgK (n w p : Nat) (G GI : List Nat) (T TI : Nat)
    (wg wx wy : List Int) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(permOK n w (mask w) (n * w) T TI,
    strictB (pidn n w) fun idn =>
      invProdP n w idn G GI T TI wg fun Z _ =>
        wordP n w idn G GI wx fun X XI =>
          wordP n w idn G GI wy fun Y YI => cfgK n w p idn Z X XI Y YI)))

end CFSG.KC.B45P

end
