module

public import Certificates.Data.Kernel.LocalQT.Tc
public import Certificates.Data.Kernel.Fi22.T46
public import Certificates.Data.Kernel.PkPow

public section

namespace CFSG.KC.LQT.U62G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.T46K CFSG.KC.LQT.TC CFSG.KC.PkPow CFSG.F4.Native

@[expose] noncomputable def gensFrom : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 46))
    (fun g _ ih j => bAnd(Nat.beq g (tT (Nat.mul (nat_lit 2) j)), ih (Nat.succ j)))

@[expose] noncomputable def gensU (G : List Nat) : Bool := gensFrom G (nat_lit 0)

@[expose] def frobU (c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + f4mul (coord c i) (coord c i) * 4 ^ i) 0

@[expose] noncomputable def phiU (Phi : Nat) : Bool :=
  bAnd(canonK (nat_lit 693) (nat_lit 12) (mask (nat_lit 12)) (nat_lit 8316) Phi,
    allN (nat_lit 693) fun i => strictB (pg (nat_lit 12) (mask (nat_lit 12)) Phi i) fun y =>
      bAnd(Nat.blt y (nat_lit 693), Nat.beq (UC y) (normC (frobU (UC i)))))

@[expose] noncomputable def wordU (G : List Nat) (w : List Int) : Nat :=
  wordTc (nat_lit 693) (nat_lit 12) (pidn (nat_lit 693) (nat_lit 12)) G G w

@[expose] def xw : List Int :=
  [30, 33, 16, 12, 9, 39, 39, 30, 33, 16, 12, 9, 39, 39, 30, 33, 16, 12, 9, 39, 39]

@[expose] def yw : List Int := [41, 46, 21, 23, 36, 41, 46, 21, 23, 36]

@[expose] noncomputable def baseU (G : List Nat) (Phi X Y : Nat) : Bool :=
  bAnd(gensU G, bAnd(phiU Phi, bAnd(Nat.beq X (wordU G xw), Nat.beq Y (wordU G yw))))

@[expose] noncomputable def classU (G : List Nat) (Phi R : Nat) (tw : List Int) (fix : Nat)
    (ws : List (List Int)) (prog : List (Int × Int)) (X Y : Nat) : Bool :=
  bAnd(Nat.beq R (pcomp (nat_lit 693) (nat_lit 12) (mask (nat_lit 12)) (wordU G tw) Phi),
    bAnd(sqIdK (nat_lit 693) (nat_lit 12) (mask (nat_lit 12)) (nat_lit 8316)
      (pidn (nat_lit 693) (nat_lit 12)) R,
    bAnd(Nat.beq (nfix (nat_lit 693) (nat_lit 12) R) fix,
      tcK (nat_lit 693) (nat_lit 12) G G R R ws prog (List.cons X (List.cons Y List.nil)))))

end CFSG.KC.LQT.U62G

end
