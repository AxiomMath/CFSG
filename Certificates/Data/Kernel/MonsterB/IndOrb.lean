module

public import Certificates.Data.Kernel.MonsterB.U6Orb

public section

namespace CFSG.KC.IndOrb

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.U6Orb

@[expose] noncomputable def anyL {α : Type} (f : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) L

@[expose] noncomputable def invTabOK (P w I wI N : Nat) : Bool :=
  strictB P fun P => strictB I fun I => allN N fun p =>
    (fun x => andB (Nat.blt x N) (Nat.beq (fget I x wI) p)) (fget P p w)

@[expose] noncomputable def inOrb (I wI N o n x : Nat) : Bool :=
  andB (Nat.blt x N) ((fun p => andB (Nat.ble o p) (Nat.blt p (Nat.add o n))) (fget I x wI))

@[expose] noncomputable def orbOK (act : Nat → Nat → Nat) (ng P w o n D wE root : Nat) : Bool :=
  strictB P fun P => strictB D fun D =>
    andB (Nat.beq (fget P o w) root) (andB (allN n fun i => allN ng fun k =>
      (fun j => andB (Nat.blt j n)
        (Nat.beq (fget P (Nat.add o j) w) (act k (fget P (Nat.add o i) w)))) (tabE ng wE D i k))
      (CFSG.KC.Bfs.replayOK (tabE ng wE D) ng n))

@[expose] noncomputable def rangeOK (G N M b o : Nat) : Bool :=
  strictB G fun G => andB (allN N fun i => Nat.blt (fget G i (nat_lit 12)) N)
    (allN M fun i => Nat.ble b (fget G (Nat.add o i) (nat_lit 12)))

@[expose] noncomputable def gen2 (G0 G1 c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) G1 G0 (Nat.beq c (nat_lit 0))

@[expose] noncomputable def wordT (G0 G1 : Nat) (w : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) i (fun c _ ih => fget (gen2 G0 G1 c) ih (nat_lit 12)) w

@[expose] noncomputable def fixOK (G0 G1 : Nat) (WS : List (List Nat)) (cs : List Nat)
    (P w o n b : Nat) : Bool :=
  strictB G0 fun G0 => strictB G1 fun G1 => strictB P fun P => allN n fun j =>
    (fun u => orB (anyL (Nat.beq u) cs) ((fun x => anyL (fun wd =>
      notB (Nat.beq (wordT G0 G1 wd x) x)) WS) (Nat.add b u))) (fget P (Nat.add o j) w)

@[expose] noncomputable def fixAt (G0 G1 : Nat) (WS : List (List Nat)) (x : Nat) : Bool :=
  strictB G0 fun G0 => strictB G1 fun G1 => allL (fun wd => Nat.beq (wordT G0 G1 wd x) x) WS

@[expose] noncomputable def keyOK (H m S I wI N o n : Nat) : Bool :=
  strictB H fun H => strictB S fun S => strictB I fun I => allN m fun i =>
    (fun x => andB (inOrb I wI N o n x) (andB
      (Nat.beq (fget S x (nat_lit 12)) (fget H (Nat.add m i) (nat_lit 12)))
      (bIf(Nat.blt (Nat.succ i) m, Nat.blt x (fget H (Nat.succ i) (nat_lit 12)), true))))
      (fget H i (nat_lit 12))

@[expose] noncomputable def zActK (G0 G1 b g x : Nat) : Nat :=
  Nat.sub (fget (gen2 G0 G1 g) (Nat.add b x) (nat_lit 12)) b

@[expose] noncomputable def sigOK (G0 G1 b P o n D S T ZI N oz nz : Nat) : Bool :=
  strictB G0 fun G0 => strictB G1 fun G1 => strictB P fun P => strictB D fun D =>
  strictB S fun S => strictB T fun T => strictB ZI fun ZI => allN n fun j =>
    (fun u => (fun v => andB (inOrb ZI (nat_lit 12) N oz nz v)
      (andB (Nat.beq (fget T v (nat_lit 12)) u) (allN (nat_lit 2) fun g =>
        Nat.beq (fget S (fget P (Nat.add o (tabE (nat_lit 2) (nat_lit 12) D j g)) (nat_lit 12))
          (nat_lit 12)) (zActK G0 G1 b g v)))) (fget S u (nat_lit 12)))
      (fget P (Nat.add o j) (nat_lit 12))

@[expose] noncomputable def tauOK (G0 G1 b P o n T ZI N : Nat) : Bool :=
  strictB G0 fun G0 => strictB G1 fun G1 => strictB P fun P => strictB T fun T =>
  strictB ZI fun ZI => allN n fun j =>
    (fun x => (fun t => andB (inOrb ZI (nat_lit 12) N o n t)
      (andB (Nat.beq (fget T t (nat_lit 12)) x) (andB (notB (Nat.beq t x)) (allN (nat_lit 2) fun g =>
        Nat.beq (fget T (zActK G0 G1 b g x) (nat_lit 12)) (zActK G0 G1 b g t))))) (fget T x (nat_lit 12)))
      (fget P (Nat.add o j) (nat_lit 12))

@[expose] noncomputable def mapOK (C P w o n b : Nat) (f : Nat → Nat) : Bool :=
  strictB C fun C => strictB P fun P => allN n fun j =>
    (fun u => Nat.beq (fget C (Nat.add b u) (nat_lit 12)) (f u)) (fget P (Nat.add o j) w)

@[expose] noncomputable def backOK (C P o n b a S I N oz nz : Nat) : Bool :=
  strictB C fun C => strictB P fun P => strictB S fun S => strictB I fun I => allN n fun j =>
    (fun x => (fun y => andB (Nat.ble a y) ((fun z => andB (inOrb I (nat_lit 12) N oz nz z)
      (Nat.beq (fget S z (nat_lit 12)) x)) (Nat.sub y a))) (fget C (Nat.add b x) (nat_lit 12)))
      (fget P (Nat.add o j) (nat_lit 12))

end CFSG.KC.IndOrb

end
