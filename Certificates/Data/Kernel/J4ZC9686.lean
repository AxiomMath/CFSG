module

public import Certificates.Data.Kernel.J4R0

public section

namespace CFSG.KC.J4ZC9686

open CFSG.KC.J4Q (mulJ getN wordJ)
open CFSG.KC.J4R0 (wK)
open CFSG.Sporadic.J4.ZCent (perfW perfWord)

variable (c rm one : Nat)

@[expose] noncomputable def invsB (B : List Nat) (b3 b4 : Nat) : List Nat :=
  [getN one B 0, getN one B 1, getN one B 2, b3, b4, getN one B 5, getN one B 6, getN one B 7,
    getN one B 8, getN one B 9, getN one B 10, getN one B 11, getN one B 12, getN one B 13,
    getN one B 14, getN one B 15]

@[expose] noncomputable def invOK (B : List Nat) : Bool :=
  (List.range 16).all fun n => Nat.beq n 3 || Nat.beq n 4 ||
    Nat.beq (mulJ c rm (getN one B n) (getN one B n)) one

@[expose] noncomputable def perfOK (B BI : List Nat) : Bool :=
  (List.range 16).all fun i =>
    Nat.beq (wordJ c rm one B BI (perfWord (perfW.getD i []))) (getN one B i)

@[expose] noncomputable def knOK (X B T : List Nat) (q : Nat) (W : List (Nat × Nat)) : Bool :=
  (List.range 16).all fun j => Nat.blt (W.getD j (0, 0)).1 60 &&
    Nat.beq (mulJ c rm q (getN one B j))
      (mulJ c rm (mulJ c rm (getN one T (W.getD j (0, 0)).1) (wK c rm one X (W.getD j (0, 0)).2 0 15))
        q)

end CFSG.KC.J4ZC9686
