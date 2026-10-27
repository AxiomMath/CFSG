module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Fi22Nbr3153

public section

namespace CFSG.KC.Co2R3

open CFSG.KC.Enum CFSG.KC.N3153

@[expose] noncomputable def at12 (A x : Nat) : Nat := pg (nat_lit 12) (nat_lit 4095) A x

@[expose] noncomputable def bitK (A x : Nat) : Bool := Nat.beq (fld(A, x, nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def memK (l : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a v, true, ih)) l

@[expose] noncomputable def cntK (n : Nat) (f : Nat → Bool) : Nat :=
  foldN n (fun w a => nIf(f w, Nat.add a (nat_lit 1), a)) (nat_lit 0)

@[expose] noncomputable def orbKey (m D P V Q y : Nat) : Nat :=
  nIf(Nat.beq (at12 D y) (nat_lit 1), Nat.mul (at12 Q y) (Nat.add m (nat_lit 1)),
    Nat.add (Nat.add (Nat.mul (at12 Q (at12 P y)) (Nat.add m (nat_lit 1))) (at12 V y)) (nat_lit 1))

@[expose] noncomputable def orbPtK (n m : Nat) (G : Nat → Nat) (L D P V Q y : Nat) : Bool :=
  bAnd(Nat.ble (nat_lit 1) (at12 D y), bIf(Nat.beq (at12 D y) (nat_lit 1),
    bAnd(Nat.beq (at12 L y) y, bAnd(Nat.beq (at12 P y) (nat_lit 0),
      bAnd(Nat.beq (at12 V y) (nat_lit 0), allN y (fun v => Nat.blt (at12 Q v) (at12 Q y))))),
    bAnd(Nat.blt (at12 V y) m, bAnd(Nat.blt (at12 P y) n,
      bAnd(Nat.beq (at12 (G (at12 V y)) (at12 P y)) y,
      bAnd(Nat.beq (at12 L y) (at12 L (at12 P y)),
      bAnd(Nat.beq (at12 D y) (Nat.add (at12 D (at12 P y)) (nat_lit 1)),
        Nat.blt (at12 Q (at12 P y)) (at12 Q y))))))))

@[expose] noncomputable def orbEdgeK (n m : Nat) (G : Nat → Nat) (D P V Q k x : Nat) : Bool :=
  strictB (at12 (G k) x) fun y => bIf(Nat.blt y n,
    bIf(Nat.beq (at12 D y) (nat_lit 1), Nat.ble (at12 Q y) (at12 Q x),
      Nat.ble (orbKey m D P V Q y)
        (Nat.add (Nat.add (Nat.mul (at12 Q x) (Nat.add m (nat_lit 1))) k) (nat_lit 1))), true)

@[expose] noncomputable def orbReplayK (n m : Nat) (G : Nat → Nat) (L D P V O Q : Nat) : Bool :=
  bAnd(allN n (fun i => bAnd(Nat.blt (at12 O i) n, Nat.beq (at12 Q (at12 O i)) i)),
  bAnd(allN n (orbPtK n m G L D P V Q),
  bAnd(allN (Nat.sub n (nat_lit 1)) (fun i => Nat.blt (orbKey m D P V Q (at12 O i))
    (orbKey m D P V Q (at12 O (Nat.add i (nat_lit 1))))),
    allN m (fun k => allN n (orbEdgeK n m G D P V Q k)))))

@[expose] noncomputable def rootsK (L : Nat) (roots : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih =>
    bAnd(Nat.blt r.1 (nat_lit 2300), bAnd(Nat.beq (at12 L r.1) r.1,
      bAnd(Nat.beq (cntK (nat_lit 2300) fun w => Nat.beq (at12 L w) r.1) r.2, ih)))) roots

@[expose] noncomputable def anyRootK (roots : List (Nat × Nat)) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => bIf(Nat.beq r.1 v, true, ih)) roots

@[expose] noncomputable def recK (m : Nat) (G : Nat → Nat) (L D P V : Nat) (roots : List (Nat × Nat)) :
    Bool :=
  bAnd(allN m (fun k => allN (nat_lit 2300) fun x => strictB (at12 (G k) x) fun y =>
    bAnd(Nat.blt y (nat_lit 2300), Nat.beq (at12 L y) (at12 L x))),
  bAnd(allN (nat_lit 2300) (fun x => bAnd(Nat.blt (at12 L x) (nat_lit 2300),
    bIf(Nat.beq (at12 D x) (nat_lit 1), Nat.beq (at12 L x) x,
      bAnd(Nat.blt (at12 P x) (nat_lit 2300),
      bAnd(Nat.beq (Nat.add (at12 D (at12 P x)) (nat_lit 1)) (at12 D x),
      bAnd(Nat.blt (at12 V x) m, Nat.beq (at12 (G (at12 V x)) (at12 P x)) x)))))),
  bAnd(allN (nat_lit 2300) (fun x => anyRootK roots (at12 L x)), rootsK L roots)))

@[expose] noncomputable def llK (n : Nat) (M : Nat → Nat) (a L : Nat) (good : List Nat) : Bool :=
  strictB (M a) fun A => allN n fun x => Bool.rec (motive := fun _ => Bool)
    (Bool.not (memK good (at12 L x))) (memK good (at12 L x)) (bitK A x)

@[expose] noncomputable def ccK (M : Nat → Nat) (a b c : Nat) : Bool :=
  strictB (M a) fun A => strictB (M b) fun B =>
    Nat.beq (cntK (nat_lit 2300) fun w => bAnd(bitK A w, bitK B w)) c

@[expose] noncomputable def cgetN (n C v : Nat) : Nat := nIf(Nat.blt v n, cget C v, nat_lit 0)

@[expose] noncomputable def clabK (n : Nat) (S : Nat → Nat) (T : Nat) (pre : List Nat) (k L : Nat)
    (roots : List Nat) : Bool :=
  strictB (colourK n S T pre k) fun C =>
    bAnd(allN n (fun x => Nat.beq (cgetN n C x) (cgetN n C (at12 L x))),
      allN roots.length fun i => allN roots.length fun j =>
        bIf(Nat.beq i j, true, Bool.not (Nat.beq (cgetN n C (roots.getD i (nat_lit 0)))
          (cgetN n C (roots.getD j (nat_lit 0))))))

end CFSG.KC.Co2R3

end
