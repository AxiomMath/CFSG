module

public import Certificates.Data.Kernel.J4TreeCol

public section

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.J4Tree.Native

@[expose] noncomputable def mmJ : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 14336)) (nat_lit 1)

@[expose] noncomputable def packMs (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => strictN ih fun p => Nat.lor x (Nat.shiftLeft p (nat_lit 14336))) l

@[expose] noncomputable def getP (P m : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul m (nat_lit 14336))) mmJ

@[expose] noncomputable def rowOfP (n t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ i)
      (Nat.ble (pIdx n (Nat.succ i) (Nat.succ i)) t)) (Nat.sub n 1)

@[expose] noncomputable def gRank (G : Mats) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ rk => rk)
    (fun t ih X rk =>
      Bool.rec (motive := fun _ => Nat)
        (strictN (rowJ G.rm X t) fun v =>
          strictN (Nat.mod X (Nat.shiftLeft (nat_lit 1) (Nat.mul t (nat_lit 128)))) fun L =>
            Bool.rec (motive := fun _ => Nat)
              (strictN (Nat.xor L (Nat.land
                  (Nat.mul (Nat.land (Nat.div L (lowBitJ v)) G.c) G.rm) (Nat.mul v G.c))) fun L' =>
                ih L' (Nat.succ rk))
              (ih L rk) (Nat.beq v 0))
        rk (Nat.beq X 0))
    112 X 0

@[expose] noncomputable def pairRunP (G : Mats) (P qp n : Nat) (cnt : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun _ ih i j t =>
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool)
          (strictB (Nat.succ i) fun i' => strictB (Nat.succ t) fun t' => ih i' i' t')
          (strictB (Nat.succ j) fun j' => strictB (Nat.succ t) fun t' => ih i j' t')
          (Nat.blt (Nat.succ j) n))
        (Nat.beq (Nat.add (fld qp 7 t)
          (gRank G (Nat.xor (Nat.xor (Nat.xor (getP P (Nat.xor i j)) (getP P i)) (getP P j)) G.one)))
          112))
    cnt

@[expose] noncomputable def pairsOKP (G : Mats) (D : CRec) (t0 cnt : Nat) : Bool :=
  let n := 2 ^ (treeWv D.k).length
  D.mode == 1 && Nat.ble (t0 + cnt) (n * (n + 1) / 2) &&
    (strictB D.qp fun qp => strictB (packMs (matsOf G (treeWv D.k))) fun P =>
      strictB (rowOfP n t0) fun i0 => strictB (i0 + (t0 - pIdx n i0 i0)) fun j0 =>
        pairRunP G P qp n cnt i0 j0 t0)

end CFSG.KC.J4TreeCol

end
