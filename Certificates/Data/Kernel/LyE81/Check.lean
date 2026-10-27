module

public import Certificates.Data.Kernel.LyS0.Check
public import Certificates.Data.Kernel.SporSch.LyMat

public section

namespace CFSG.KD.LyE81

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KD.LyS0

@[expose] noncomputable def vec (v M : Nat) : Nat :=
  vecR 5 12 1332 111 8 CFSG.KD.OrdLy.LV CFSG.KD.OrdLy.HV CFSG.KD.OrdLy.RM v M

@[expose] noncomputable def pw (M e : Nat) : Nat :=
  CFSG.KS.SporSch.LyM.powR 5 12 1332 111 8 CFSG.KD.OrdLy.L CFSG.KD.OrdLy.H CFSG.KD.OrdLy.CM
    CFSG.KD.OrdLy.RM CFSG.KD.OrdLy.ONE M e

@[expose] noncomputable def powLK (M e : Nat) : Nat := nIf(Nat.beq e 1, M, pw M e)

@[expose] noncomputable def wordK (G : Nat → Nat) (w : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => strictN (mul acc (powLK (G x.1) x.2)) ih) w CFSG.KD.OrdLy.ONE

@[expose] noncomputable def slpR5 (A B : Nat) : Nat := mul (mul A B) (mul (mul A B) B)

@[expose] noncomputable def slpR6 (A B : Nat) : Nat := mul (mul A B) (slpR5 A B)

@[expose] noncomputable def slpR9 (A B : Nat) : Nat := mul B (slpR5 A B)

@[expose] noncomputable def slpR7 (A B : Nat) : Nat := mul (slpR6 A B) (mul A B)

@[expose] noncomputable def slpR2 (A B : Nat) : Nat := mul (slpR7 A B) (mul (slpR7 A B) (slpR7 A B))

@[expose] noncomputable def pcK (P : Nat → Nat) (cubeW : Array (List (Nat × Nat)))
    (commW : Array (Array (List (Nat × Nat)))) : Bool :=
  (List.range 7).all (fun i =>
    (cubeW[i]!).all (fun x => decide (i < x.1 ∧ x.1 < 7)) &&
      Nat.beq (wordK P [(i, 3)]) (wordK P cubeW[i]!) &&
      (List.range 7).all (fun j => decide (j ≤ i) ||
        (((commW[i]!)[j]!).all (fun x => decide (i < x.1 ∧ x.1 < 7)) &&
          Nat.beq (wordK P [(i, 1), (j, 1)]) (wordK P ((commW[i]!)[j]! ++ [(i, 1)])))))

@[expose] noncomputable def ln (x j : Nat) : Nat := fld(x, Nat.mul 12 j, 4095)

@[expose] noncomputable def trK (X Y : Nat) : Bool :=
  bAnd(vld Y, allN 111 (fun i => allBlk 0 (fun j =>
    Nat.beq (ln X (Nat.add (Nat.mul 111 i) j)) (ln Y (Nat.add (Nat.mul 111 j) i))) 111))

@[expose] noncomputable def vldV (x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x 1332) 0, allBlk 0 (fun j => Nat.blt (ln x j) 5) 111)

@[expose] noncomputable def UV (x : Nat) : Array Nat := Array.ofFn (n := 111) fun j => ln x j.val

@[expose] noncomputable def posK (PA LA : Nat → Nat) (j : Nat) : Nat :=
  Nat.add (Nat.mul 7 (PA j)) (LA j)

@[expose] noncomputable def orbAt (M V : Nat → Nat) (E : Nat → Nat → Nat) (PA LA : Nat → Nat)
    (i : Nat) : Bool :=
  bAnd(vldV (V i), bAnd(allBlk 0 (fun k => strictB (E i k) (fun e =>
      bAnd(Nat.blt e 2187, bAnd(Nat.beq (V e) (vec (V i) (M k)),
        bIf(Nat.beq e 0, true, Nat.ble (posK PA LA e) (Nat.add (Nat.mul 7 i) k)))))) 7,
    bIf(Nat.beq i 0, bAnd(Nat.beq (PA 0) 0, Nat.beq (LA 0) 0),
      bAnd(Nat.blt (PA i) i, bAnd(Nat.blt (LA i) 7, bAnd(Nat.beq (E (PA i) (LA i)) i,
        bIf(Nat.beq i 2186, true, Nat.blt (posK PA LA i) (posK PA LA (Nat.succ i)))))))))

@[expose] noncomputable def orbK (M V : Nat → Nat) (E : Nat → Nat → Nat) (PA LA : Nat → Nat)
    (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i (fun i => orbAt M V E PA LA i)) len

@[expose] noncomputable def keyK (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.add (Nat.mul acc 5) (ln x j)) 111

@[expose] noncomputable def sortK (V SO SOI : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i (fun i =>
    CFSG.KS.SporSch.LyM.sortB (fun j => keyK (V j)) SO SOI 2187 i)) len

@[expose] noncomputable def edK (E : Nat → Nat → Nat) (x k : Nat) : Nat :=
  nIf(bAnd(Nat.blt x 2187, Nat.blt k 7), E x k, 0)

@[expose] noncomputable def tbK (F : Nat → Nat) (i : Nat) : Nat := nIf(Nat.blt i 2187, F i, 0)

@[expose] noncomputable def mulIdxK (E : Nat → Nat → Nat) (PA LA : Nat → Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ j => j)
    (fun _ ih i j => nIf(Nat.beq i 0, j, edK E (ih (tbK PA i) j) (tbK LA i)))

@[expose] def tabG (m N : Nat) (mul : Nat → Nat → Nat) (ed : Nat → Nat → Nat) (idZ : Nat)
    (sets : List (List Nat)) : Bool :=
  decide (0 < idZ ∧ idZ < N) && (mul idZ (mul idZ idZ) == 0) &&
  (List.range m).all (fun k => ed idZ k == mul idZ (ed 0 k)) &&
  sets.all (fun s => decide (81 ≤ s.length) && decide (s.Pairwise (· < ·)) &&
    s.all (fun a => decide (a < N)) && s.contains idZ &&
    s.all (fun a => (mul a (mul a a) == 0) && s.all fun b => mul a b == mul b a)) &&
  (List.range N).all (fun i =>
    (mul i (mul i i) != 0) || i == 0 || i == idZ || i == mul idZ idZ ||
      sets.any (fun s => s.contains i))

end CFSG.KD.LyE81

end
