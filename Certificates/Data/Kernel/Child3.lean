module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.Child3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def forestK (n w : Nat) (PS : Nat → Nat) (kS : Nat) (roots : List Nat)
    (FP FL FD : Nat → Nat) : Bool :=
  allN n (fun p => bIf(bAnd(Nat.beq (FD p) 0, roots.contains p), true,
    bAnd(Nat.blt (FP p) n, bAnd(Nat.blt (FL p) kS, bAnd(Nat.blt (FD (FP p)) (FD p),
      Nat.beq (pg w (mask w) (PS (FL p)) (FP p)) p)))))

@[expose] noncomputable def wv (n w : Nat) (PS PSI : Nat → Nat) (wd : List Int) : Nat :=
  wordK n w (mask w) (pidn n w) PS PSI wd

@[expose] noncomputable def stabK (n w : Nat) (PS PSI : Nat → Nat) (kS r : Nat)
    (ws : List (List Int)) : Bool :=
  bAnd(Nat.blt r n, bAnd(ws.all (fun wd => lettersK kS wd),
  bAnd(ws.all (fun wd => Nat.beq (pg w (mask w) (wv n w PS PSI wd) r) r),
    allN n (fun q => bIf(Nat.beq q r, true,
      ws.any (fun wd => bIf(Nat.beq (pg w (mask w) (wv n w PS PSI wd) q) q, false, true)))))))

@[expose] noncomputable def cj (n w : Nat) (GP GIP : Nat → Nat) (l Y : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (GP l) Y) (GIP l)

@[expose] noncomputable def repK (n w : Nat) (GP GIP : Nat → Nat) (g : Nat) (CS OFF : List Nat)
    (CI E P L K S SI : Nat → Nat) (N cap j : Nat) : Bool :=
  strictB (CI j) (fun i => strictB (lget OFF i) (fun o => strictB (lget CS i) (fun c =>
  strictB (Nat.sub j o) (fun k =>
  bAnd(Nat.blt i CS.length, bAnd(Nat.ble o j, bAnd(Nat.blt k c, bAnd(Nat.ble c cap,
  bAnd(canonK n w (mask w) (Nat.mul n w) (E j),
  bAnd(bIf(Nat.beq k 0, true, bAnd(Nat.blt (P j) k, bAnd(Nat.blt (L j) g,
    Nat.beq (cj n w GP GIP (L j) (E (Nat.add o (P j)))) (E j)))),
  bAnd(bIf(Nat.beq k 0, true, bIf(Nat.blt (Nat.succ k) c,
    lexLtK (P j) (L j) (P (Nat.succ j)) (L (Nat.succ j)), true)),
  bAnd(allN g (fun l => strictB (K (Nat.add (Nat.mul g j) l)) (fun q => bAnd(Nat.blt q c,
    bAnd(Nat.beq (E (Nat.add o q)) (cj n w GP GIP l (E j)),
      bIf(Nat.beq q 0, true, bIf(lexLtK k l (P (Nat.add o q)) (L (Nat.add o q)), false, true)))))),
  bAnd(Nat.blt (S j) N, bAnd(Nat.blt (SI j) N, bAnd(Nat.beq (S (SI j)) j,
    bIf(Nat.blt (Nat.succ j) N, Nat.blt (E (S j)) (E (S (Nat.succ j))), true))))))))))))))))

@[expose] noncomputable def offOK (CS OFF : List Nat) (N : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun s O => bAnd(Nat.beq s N, List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) O))
    (fun c _ ih s O => List.rec (motive := fun _ => Bool) false
      (fun o O' _ => bAnd(Nat.beq o s, ih (Nat.add s c) O')) O) CS 0 OFF

@[expose] noncomputable def sumF (m : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i s => strictN s (fun s' => Nat.add s' (f i))) m

@[expose] noncomputable def invCount2 (n w : Nat) (LR TR : Nat → Nat) : Nat :=
  strictN (LR 0) (fun R0 => strictN (LR 1) (fun R1 =>
  sumF (rcnt R0) (fun a => sumF (rcnt R1) (fun b =>
    strictN (pcomp n w (mask w) (TR (Nat.add (roff n (Nat.mul n w) R0) a))
      (TR (Nat.add (roff n (Nat.mul n w) R1) b))) (fun X =>
      nIf(bAnd(Nat.beq (pcomp n w (mask w) X X) (pidn n w),
        bIf(Nat.beq X (pidn n w), false, true)), 1, 0))))))

end CFSG.KC.Child3

end
