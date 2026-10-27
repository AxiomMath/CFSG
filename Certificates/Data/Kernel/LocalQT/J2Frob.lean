module

public import Certificates.Data.Kernel.LocalQT.TcP

public section

namespace CFSG.KC.LQT.TC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def frobK (n w : Nat) (G GI : List Nat) (xw gw : List Int) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI,
    wordP n w (pidn n w) G GI xw fun X XI => wordP n w (pidn n w) G GI gw fun Gx GxI =>
      strictB (pcomp n w (mask w) (pcomp n w (mask w) Gx X) GxI) fun Y =>
      strictB (pcomp n w (mask w) Gx (pcomp n w (mask w) XI GxI)) fun YI =>
      strictB (pcomp n w (mask w) X X) fun X2 =>
        bAnd(Nat.beq (pcomp n w (mask w) X2 (pcomp n w (mask w) X2 X)) (pidn n w),
        bAnd(bIf(Nat.beq X (pidn n w), false, true),
        bAnd(Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X),
          Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) Gx Y) GxI)
            (pcomp n w (mask w) YI XI))))))

@[expose] noncomputable def pcK (n w N : Nat) (G GI : List Nat) (E : Nat → Nat)
    (data : List (Nat × Nat × List (List Int) × List (Int × Int))) (targets : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(Nat.beq (List.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun _ _ ih2 => Nat.succ ih2) e.2.2.1) (nat_lit 2),
      bAnd(Nat.blt e.1 N, bAnd(Nat.blt e.2.1 N,
        bAnd(mcP n w G GI [E e.1, E e.2.1] [E e.1, E e.2.1] e.2.2.1 e.2.2.2 targets, ih)))))
    data

end CFSG.KC.LQT.TC

end
