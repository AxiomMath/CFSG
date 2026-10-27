module

public import Certificates.Data.Kernel.HSIdent
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace Certificates.Kernel.HSPinned6101

open CFSG.Sporadic.Recognition.HSPinned.Native Certificates.Kernel.HSIdent

@[expose] noncomputable def g14 (T i : Nat) : Nat := fld(T, Nat.mul 14 i, 16383)

@[expose] noncomputable def g7 (T i : Nat) : Nat := fld(T, Nat.mul 7 i, 127)

@[expose] noncomputable def g1100 (T i : Nat) : Nat :=
  fld(T, Nat.mul 1100 i, Nat.sub (Nat.pow 2 1100) 1)

@[expose] noncomputable def allR (lo cnt : Nat) (f : Nat → Bool) : Bool :=
  CFSG.KC.Loop.allBelow cnt (Nat.add (Nat.shiftRight cnt 6) 1) fun i => f (Nat.add lo i)

@[expose] noncomputable def lexB (a b c d : Nat) : Bool := Nat.blt a c || (Nat.beq a c && Nat.blt b d)

@[expose] noncomputable def imgK (VAB off v : Nat) : Nat :=
  Nat.add (Nat.mul 100 (g7 VAB (Nat.add off (Nat.div v 100)))) (g7 VAB (Nat.add off (Nat.mod v 100)))

structure PD where
  n : Nat
  P : Nat
  TA : Nat
  TB : Nat
  PR : Nat
  LB : Nat
  PS : Nat

@[expose] noncomputable def headOK (D : PD) (root : Nat) : Bool :=
  Nat.blt 0 D.n && Nat.ble D.n 10000 && Nat.beq (g14 D.P 0) root && Nat.beq (g14 D.PR 0) 0 &&
    Nat.beq (g14 D.LB 0) 0

@[expose] noncomputable def pairAt (D : PD) (VAB y : Nat) : Bool :=
  Nat.blt (g14 D.P y) 10000 && Nat.blt (g14 D.TA y) D.n && Nat.blt (g14 D.TB y) D.n &&
    Nat.beq (imgK VAB 0 (g14 D.P y)) (g14 D.P (g14 D.TA y)) &&
    Nat.beq (imgK VAB 100 (g14 D.P y)) (g14 D.P (g14 D.TB y)) &&
    Nat.beq (g14 D.PS (g14 D.P y)) y &&
    (Nat.beq y 0 || (Nat.blt (g14 D.PR y) y &&
      ((Nat.beq (g14 D.LB y) 1 && Nat.beq (g14 D.TA (g14 D.PR y)) y) ||
        (Nat.beq (g14 D.LB y) 2 && Nat.beq (g14 D.TB (g14 D.PR y)) y)))) &&
    (Nat.beq y 0 || Nat.ble D.n (Nat.add y 1) ||
      lexB (g14 D.PR y) (g14 D.LB y) (g14 D.PR (Nat.add y 1)) (g14 D.LB (Nat.add y 1))) &&
    (Nat.beq (g14 D.TA y) 0 ||
      !lexB y 1 (g14 D.PR (g14 D.TA y)) (g14 D.LB (g14 D.TA y))) &&
    (Nat.beq (g14 D.TB y) 0 ||
      !lexB y 2 (g14 D.PR (g14 D.TB y)) (g14 D.LB (g14 D.TB y)))

@[expose] noncomputable def posAt (D : PD) (v : Nat) : Bool :=
  Nat.beq (g14 D.PS v) 10000 || (Nat.blt (g14 D.PS v) D.n && Nat.beq (g14 D.P (g14 D.PS v)) v)

@[expose] noncomputable def coverAt (D : PD) (c : Nat → Nat → Bool) (x y : Nat) : Bool :=
  !c x y || Nat.blt (g14 D.PS (Nat.add (Nat.mul 100 x) y)) D.n

@[expose] noncomputable def adjK (LM x y : Nat) : Bool :=
  !Nat.beq x y && !Nat.beq (Nat.land (g1100 LM x) (g1100 LM y)) 0

@[expose] noncomputable def nonK (LM x y : Nat) : Bool := !Nat.beq x y && !adjK LM x y

@[expose] noncomputable def vabAt (VAB i : Nat) : Bool :=
  Nat.beq vtxA[i]! (g7 VAB i) && Nat.beq vtxB[i]! (g7 VAB (Nat.add 100 i))

@[expose] noncomputable def lmAt (LM i : Nat) : Bool := Nat.beq (lmask stars[i]!) (g1100 LM i)

@[expose] noncomputable def starAt (fa fb : Nat → Nat) (VAB i : Nat) : Bool :=
  Nat.beq (stars[i]!).length 22 && decide (stars[i]!).Nodup &&
    (stars[i]!).all fun x =>
      (stars[g7 VAB i]!).contains (fa x) && (stars[g7 VAB (Nat.add 100 i)]!).contains (fb x)

@[expose] noncomputable def injAt (LM i j : Nat) : Bool :=
  Nat.beq i j || !Nat.beq (g1100 LM i) (g1100 LM j)

@[expose] noncomputable def witAt (LM k : Nat) : Bool :=
  Nat.blt (wit[k]!).1 100 && Nat.blt (wit[k]!).2 100 &&
    Nat.blt (CFSG.Sporadic.HS.Native.hsData.basis[k]!) 1100 &&
    Nat.beq (Nat.land (g1100 LM (wit[k]!).1) (g1100 LM (wit[k]!).2))
      (Nat.pow 2 (CFSG.Sporadic.HS.Native.hsData.basis[k]!))

end Certificates.Kernel.HSPinned6101

end
