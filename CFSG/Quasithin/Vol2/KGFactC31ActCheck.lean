module

public import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def conjTab (n : Nat) (x xi t : Table) : Table := compT n (compT n x t) xi

@[expose] def badAct (n m : Nat) (x xi t : Table) : Bool :=
  !(tblEq n (conjTab n x xi t) t) &&
    (List.range m).all fun j =>
      tblEq n (compT n t (conjTab n (powT n j x) (powT n j xi) t))
        (compT n (conjTab n (powT n j x) (powT n j xi) t) t)

@[expose] def powTabs (n : Nat) (x : Table) (m : Nat) : List Table :=
  (List.range m).map fun a => powT n a x

@[expose] def gridTabs (n : Nat) (x y : Table) (p q : Nat) : List Table :=
  (List.range p).flatMap fun a => (List.range q).map fun b => compT n (powT n a x) (powT n b y)

@[expose] def gridInj (n : Nat) (x y : Table) (p : Nat) : Bool :=
  (List.range p).all fun a => (List.range p).all fun b => (List.range p).all fun c =>
    (List.range p).all fun d => (a == c && b == d) ||
      !(tblEq n (compT n (powT n a x) (powT n b y)) (compT n (powT n c x) (powT n d y)))

@[expose] def actCheck (n m : Nat) (invs els : List Table) : Bool :=
  els.all fun e => invOK n e (invT n e) && invs.all fun t => !(badAct n m e (invT n e) t)

end CFSG.Quasithin.KGC31.Native

end
