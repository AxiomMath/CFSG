module

public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def maskProd (n : Nat) : List Table → Nat → Table
  | [], _ => idT n
  | b :: bs, mask => compT n (if mask % 2 = 1 then b else idT n) (maskProd n bs (mask / 2))

@[expose] def spanTabs (n : Nat) (bs : List Table) : List Table :=
  (List.range (2 ^ bs.length)).map (maskProd n bs)

@[expose] def orbTabs (n m : Nat) (x xi t : Table) : List Table :=
  (List.range m).map fun j => conjTab n (powT n j x) (powT n j xi) t

@[expose] def orbIs (n : Nat) (orb bs : List Table) : Bool :=
  (orb.all fun o => (spanTabs n bs).any (tblEq n o)) &&
    bs.all fun b => (spanTabs n orb).any (tblEq n b)

@[expose] def orbCheck (n m : Nat) (invs els : List Table) (cands : List (List Table)) : Bool :=
  els.all fun e => invOK n e (invT n e) && invs.all fun t =>
    !(badAct n m e (invT n e) t) || cands.any (orbIs n (orbTabs n m e (invT n e) t))

@[expose] def ebasisOK (n : Nat) (bs : List Table) : Bool :=
  (bs.all fun b => tblEq n (compT n b b) (idT n)) &&
    (bs.all fun b => bs.all fun c => commT n b c) &&
    (List.range (2 ^ bs.length)).all fun mask =>
      mask == 0 || !(tblEq n (maskProd n bs mask) (idT n))

@[expose] def compEq (n : Nat) (T b u : Table) : Bool :=
  allIn 0 n fun i => ap T (ap b i) == ap u (ap T i)

@[expose] def normAll (n : Nat) (bs : List Table) : Table → Bool :=
  let sp := spanTabs n bs
  fun T => bs.all fun b => sp.any fun u => compEq n T b u

@[expose] def masksOK (n : Nat) (bs : List Table) (g : Table) (masks : List Nat) : Bool :=
  bs.length == masks.length &&
    (bs.zip masks).all fun p => tblEq n (compT n g p.1) (compT n (maskProd n bs p.2) g)

end CFSG.Quasithin.KGC31.Native

end
