module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.Sp6Root

open CFSG.KC.Enum CFSG.KS CFSG.KS.M11

@[expose] noncomputable def commQ (n w m P : Nat) (QL : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun Q _ ih =>
    bAnd(strictB (pcomp n w m (pcomp n w m Q P) (pcomp n w m Q Q))
      (fun C => Nat.beq (pcomp n w m P C) (pcomp n w m C P)), ih)) QL

@[expose] noncomputable def k1P (n w m idn : Nat) (QL : List Nat) (P : Nat) : Bool :=
  bAnd(ordIs n w m idn P (nat_lit 1), commQ n w m P QL)

@[expose] noncomputable def rowK (n w m idn X : Nat) (S0 : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun Y _ ih =>
    bIf(ordIs n w m idn (pcomp n w m X Y) (nat_lit 3), false, ih)) S0

@[expose] noncomputable def pairsK (n w m idn : Nat) (S0 S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun X _ ih => bAnd(rowK n w m idn X S0, ih)) S

end CFSG.KS.Sp6Root

end
