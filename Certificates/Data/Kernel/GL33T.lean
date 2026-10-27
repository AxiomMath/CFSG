module

public import Certificates.Data.Kernel.GL33K

public noncomputable section

namespace CFSG.KC.GL33T

open CFSG.KC.GL33K

@[expose] def lenK {α : Type} (L : List α) : Nat := List.rec 0 (fun _ _ ih => Nat.succ ih) L

@[expose] def bitT (M c : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 c))

@[expose] def setT (M c : Nat) : Nat := Nat.lor M (Nat.shiftLeft 1 c)

@[expose] def getT (L : List Nat) (l : Nat) : Nat :=
  List.rec (fun _ => 0) (fun a _ ih k => Nat.rec a (fun k' _ => ih k') k) L l

@[expose] def getF (L : List Nat) (dflt l : Nat) : Nat :=
  List.rec (fun _ => dflt) (fun a _ ih k => Nat.rec a (fun k' _ => ih k') k) L l

@[expose] def getG (L : List Nat) (l : Nat) : Nat :=
  List.rec (fun _ => oneK) (fun a _ ih k => Nat.rec a (fun k' _ => ih k') k) L l

@[expose] def zipK {α β : Type} (p : α → β → Bool) (A : List α) : List β → Bool :=
  List.rec (fun B => List.rec true (fun _ _ _ => false) B)
    (fun a _ ih B => List.rec false (fun b B' _ => p a b && ih B') B) A

@[expose] def uptoK (p : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec true (fun k ih => ih && p k) n

@[expose] def actT (u b : Nat) : Nat := Nat.mod (mulK u b) 27

@[expose] def negT (r : Nat) : Nat :=
  (2 * (r % 3)) % 3 + 3 * ((2 * ((r / 3) % 3)) % 3) + 9 * ((2 * ((r / 9) % 3)) % 3)

@[expose] def detT (c : Nat) : Bool :=
  let a0 := (c % 27) % 3
  let a1 := ((c % 27) / 3) % 3
  let a2 := ((c % 27) / 9) % 3
  let b0 := ((c / 27) % 27) % 3
  let b1 := (((c / 27) % 27) / 3) % 3
  let b2 := (((c / 27) % 27) / 9) % 3
  let c0 := ((c / 729) % 27) % 3
  let c1 := (((c / 729) % 27) / 3) % 3
  let c2 := (((c / 729) % 27) / 9) % 3
  !Nat.beq ((a0 * b1 * c2 + a1 * b2 * c0 + a2 * b0 * c1 +
    2 * (a0 * b2 * c1 + a1 * b0 * c2 + a2 * b1 * c0)) % 3) 0

@[expose] def blockT (c : Nat) : Bool := Nat.beq ((c / 27) % 3) 0 && Nat.beq ((c / 729) % 3) 0

@[expose] def treeT (gens : List Nat) (M : Nat) (R : List (Nat × Nat × Nat)) : Nat → Bool :=
  List.rec (fun S => Nat.beq S M)
    (fun r _ ih S => bitT S r.2.1 && !bitT S r.1 && Nat.beq r.1 (mulK r.2.1 (getG gens r.2.2)) &&
      ih (setT S r.1)) R

@[expose] def closT (gens : List Nat) (M : Nat) (R : List (Nat × Nat × Nat)) : Bool :=
  allK (fun g => bitT M (mulK oneK g)) gens &&
    allK (fun r => allK (fun g => bitT M (mulK r.1 g)) gens) R

@[expose] def memT (gens : List Nat) (M : Nat) (R : List (Nat × Nat × Nat)) : Bool :=
  treeT gens M R (setT 0 oneK) && closT gens M R

@[expose] def stabN (R : List (Nat × Nat × Nat)) : Nat :=
  List.rec 1 (fun r _ ih => Bool.rec ih (Nat.succ ih) (Nat.beq (r.1 % 27) 1)) R

@[expose] def stabM (R : List (Nat × Nat × Nat)) : Nat :=
  List.rec (setT 0 oneK) (fun r _ ih => Bool.rec ih (setT ih r.1) (Nat.beq (r.1 % 27) 1)) R

@[expose] def stabL (R : List (Nat × Nat × Nat)) : List Nat :=
  List.rec [oneK] (fun r _ ih => Bool.rec ih (r.1 :: ih) (Nat.beq (r.1 % 27) 1)) R

@[expose] def orbM (R : List (Nat × Nat × Nat)) : Nat :=
  List.rec (setT 0 1) (fun r _ ih => setT ih (r.1 % 27)) R

@[expose] def evalW (L : List Nat) (w : List Nat) : Nat :=
  List.rec (fun acc => acc) (fun l _ ih acc => ih (mulK acc (getG L l))) w oneK

@[expose] def covT (M : Nat) (reps : List Nat) (blk : Bool) (C : List (Nat × Nat)) : Bool :=
  Nat.beq (lenK C) 729 && allK (fun t => Nat.blt t 19683) reps &&
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih a => (!detT (1 + 27 * a) || (blk && !blockT (1 + 27 * a)) ||
      bitT M r.1 && Nat.beq (1 + 27 * a) (mulK r.1 (getF reps 19683 r.2))) && ih (Nat.succ a)) C) 0

@[expose] def dBadT (Q : List Nat) (y : Nat) : Bool :=
  (Nat.beq (y % 27) 1 || Nat.beq (y % 27) 2) &&
    (!blockT y || !(List.rec false (fun d _ ih =>
      (Nat.beq (actT 3 y) (actT 3 d) && Nat.beq (actT 9 y) (actT 9 d)) ||
      (Nat.beq (actT 3 y) (negT (actT 3 d)) && Nat.beq (actT 9 y) (negT (actT 9 d))) || ih) Q))

@[expose] def childT (gens : List Nat) (M QM : Nat) (Q : List Nat) (gj : List Nat) (Mj : Nat)
    (x kind : Nat) (ws : List (List Nat)) : Bool :=
  Nat.rec (bitT M x)
    (fun k _ => Nat.rec
      (zipK (fun g w => Nat.beq g (evalW (gens ++ [x]) w)) gj ws &&
        allK (fun g => bitT Mj g) gens && bitT Mj x)
      (fun k _ => Nat.rec
        (allK (fun w => Nat.beq (evalW (gens ++ [x]) w % 27) 1 &&
          !bitT QM (evalW (gens ++ [x]) w)) ws)
        (fun _ _ => allK (fun w => dBadT Q (evalW (gens ++ [x]) w)) ws) k) k) kind

@[expose] def phiT (gens : List Nat) (M : Nat) (R : List (Nat × Nat × Nat))
    (kind u1 u2 g1 g2 g3 : Nat) : Bool :=
  Nat.rec (allK (fun g => Nat.beq (g % 27) 1 || Nat.beq (g % 27) 2) gens)
    (fun k _ => Nat.rec
      (allK blockT gens && uptoK (fun u => Nat.beq (u % 3) 0 || bitT (orbM R) u ||
        bitT (orbM R) (negT u)) 27)
      (fun _ _ =>
        Nat.blt u1 27 && Nat.blt u2 27 && Nat.beq (u1 % 3) 0 && Nat.beq (u2 % 3) 0 &&
        !Nat.beq (((u1 / 3) % 3 * ((u2 / 9) % 3) + 2 * ((u1 / 9) % 3 * ((u2 / 3) % 3))) % 3) 0 &&
        allK (fun g => allK (fun x => elemK (actT x g) [1, 2, u1, negT u1, u2, negT u2])
          [1, 2, u1, negT u1, u2, negT u2]) gens &&
        bitT M g1 && Nat.beq (actT 1 g1) 2 && Nat.beq (actT u1 g1) u1 && Nat.beq (actT u2 g1) u2 &&
        bitT M g2 && Nat.beq (actT 1 g2) u1 && Nat.beq (actT u1 g2) 1 && Nat.beq (actT u2 g2) u2 &&
        bitT M g3 && Nat.beq (actT 1 g3) u1 && Nat.beq (actT u1 g3) u2 && Nat.beq (actT u2 g3) 1)
      k) kind

@[expose] def deadT (R : List (Nat × Nat × Nat)) : Bool := !Nat.beq (8 % stabN R) 0

@[expose] def abelT (R : List (Nat × Nat × Nat)) : Bool :=
  Nat.beq (stabN R) 8 &&
    allK (fun a => allK (fun b => Nat.beq (mulK a b) (mulK b a)) (stabL R)) (stabL R)

@[expose] def childK (G : List (List Nat)) (Ms : List Nat) (i : Nat) (g : List Nat) (M QM : Nat)
    (Q : List Nat) (x : Nat) (c : Nat × Nat × List (List Nat)) : Bool :=
  (!Nat.beq c.1 1 || Nat.blt i c.2.1 && Nat.blt c.2.1 (lenK G)) &&
    childT g M QM Q (List.getD G c.2.1 []) (List.getD Ms c.2.1 0) x c.1 c.2.2

@[expose] def stage1K (G : List (List Nat)) (Ms : List Nat) (i : Nat) (g : List Nat)
    (R : List (Nat × Nat × Nat)) (M : Nat) (reps : List Nat) (cov : List (Nat × Nat))
    (chs : List (List (Nat × Nat × List (List Nat)))) : Bool :=
  !Nat.beq (stabN R) 8 && covT M reps true cov &&
    zipK (childK G Ms i g M 0 []) reps (List.getD chs 0 [])

@[expose] def ucovK (OM M : Nat) (orr : List Nat) (C : List (Nat × Nat)) : Bool :=
  Nat.beq (lenK C) 26 &&
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih u => (bitT OM u || bitT M r.1 && Nat.beq (actT u r.1) (getF orr 27 r.2)) &&
      ih (Nat.succ u)) C) 1

@[expose] def stage2K (G : List (List Nat)) (Ms : List Nat) (i : Nat) (g : List Nat)
    (R : List (Nat × Nat × Nat)) (M QM : Nat) (qreps orr org ori : List Nat)
    (uc : List (Nat × Nat)) (pw : List Nat)
    (chs : List (List (Nat × Nat × List (List Nat)))) : Bool :=
  Nat.beq (stabN R) 8 && Nat.beq (stabM R) QM &&
    phiT g M R (getT pw 0) (getT pw 1) (getT pw 2) (getT pw 3) (getT pw 4) (getT pw 5) &&
    zipK (fun r h => Nat.beq (h % 27) r && Nat.blt h 19683) orr org &&
    zipK (fun h h' => Nat.beq (mulK h h') oneK) org ori &&
    ucovK (orbM R) M orr uc &&
    zipK (fun h grp => zipK (fun t c => childK G Ms i g M QM (stabL R) (mulK t h) c) qreps grp)
      org chs

@[expose] def nodeK (G : List (List Nat)) (Ms : List Nat) (i : Nat) (g : List Nat)
    (R : List (Nat × Nat × Nat)) (M kind QM : Nat) (qreps reps : List Nat)
    (cov : List (Nat × Nat)) (orr org ori : List Nat) (uc : List (Nat × Nat)) (pw : List Nat)
    (chs : List (List (Nat × Nat × List (List Nat)))) : Bool :=
  memT g M R &&
    Nat.rec (deadT R)
      (fun k _ => Nat.rec (stage1K G Ms i g R M reps cov chs)
        (fun k _ => Nat.rec (abelT R)
          (fun k _ => Nat.rec (stage2K G Ms i g R M QM qreps orr org ori uc pw chs)
            (fun _ _ => false) k) k) k) kind

end CFSG.KC.GL33T

end
