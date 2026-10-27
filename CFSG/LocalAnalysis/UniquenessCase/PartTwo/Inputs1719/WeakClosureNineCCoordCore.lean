module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

open CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

@[expose] def eList (T : List (List Nat)) (Es : List (List (List Nat))) : List (List (List Nat)) :=
  [cid] :: (((invs T).map fun a => [cid, a]) ++ Es)

@[expose] def actB (y u : List Nat) (a b : Nat) : Bool :=
  cmul u y == cmul (cpow y a) u && cmul y u == cmul u (cpow y b) && cpow y a != y

@[expose] def threeB (T : List (List Nat)) (y : List Nat) (p : Nat)
    (w : List (List Nat × Nat × List Nat)) : Bool :=
  p == 3 || (w.all (fun t => T.contains t.1 && cmul t.1 (cpow y t.2.1) == cmul t.2.2 t.1) &&
    cpow ((w.map fun t => t.2.2).foldl cmul cid) 3 == cid &&
    (w.map fun t => t.2.2).foldl cmul cid != cid)

structure MovW where
  k : Nat
  u : List Nat
  a : Nat
  b : Nat
  w : List (List Nat × Nat × List Nat)

@[expose] def movCheck (T : List (List Nat)) (D : KData) (E : List (List Nat)) (m : MovW) : Bool :=
  normB E D.K.lit && D.K.lit.contains m.u && T.contains m.u && actB D.y m.u m.a m.b &&
    threeB T D.y D.p m.w

@[expose] def movAll (T : List (List Nat)) (Hs : List KData) (El : List (List (List Nat)))
    (ms : List MovW) : Bool :=
  El.length == ms.length && (El.zip ms).all fun em =>
    decide (em.2.k < Hs.length) && movCheck T (Hs.getD em.2.k KData.dflt) em.1 em.2

structure FixW where
  k : Nat
  e : List Nat
  κ : List Nat
  c : List Nat
  j : Nat
  w : List (List Nat × Nat × List Nat)

@[expose] def fixCheck (T : List (List Nat)) (D : KData) (E : List (List Nat)) (f : FixW) : Bool :=
  E.all D.K.lit.contains && E.contains f.e && D.K.lit.contains f.κ &&
    cmul f.κ f.e == cmul f.c f.κ && cpow (cpow (cmul f.e f.c) f.j) D.p == cid &&
    cpow (cmul f.e f.c) f.j != cid && threeB T D.y D.p f.w

@[expose] def fixAll (T : List (List Nat)) (Ks : List KData) (El : List (List (List Nat)))
    (fs : List (Option FixW)) (Est : List (List Nat)) : Bool :=
  El.length == fs.length && (El.zip fs).all fun ef => match ef.2 with
    | some f => decide (f.k < Ks.length) && fixCheck T (Ks.getD f.k KData.dflt) ef.1 f
    | none => ef.1 == [cid] || setEq ef.1 Est

structure PairC where
  x : List Nat
  l : List Nat
  t : List Nat
  s₁ : List Nat
  s₂ : List Nat

@[expose] def pairCCheck (T Lc : List (List Nat)) (ws : List PairC) : Bool :=
  (invs T).all fun x => !(T.all (ccomm x)) || ws.any fun w => w.x == x && Lc.contains w.l &&
    Lc.contains w.t && T.contains w.s₁ && T.contains w.s₂ && cmul w.t x == cmul w.s₁ w.t &&
    cmul (cmul w.t w.l) x == cmul (cmul w.s₂ w.t) w.l && !(ccomm w.s₁ w.s₂)

@[expose] def starCheck (T : List (List Nat)) (D : KData) (Est E : List (List Nat)) (m : MovW) :
    Bool :=
  D.p == 3 && movCheck T D E m && normB Est D.K.lit &&
    Est.all fun e => cinvol e && (List.range 3).all fun j =>
      D.N2.lit.contains (cmul (cmul (cmul e (cpow D.y j)) e) (cpow D.y (3 - j)))

@[expose] def starAll (T : List (List Nat)) (Hs : List KData) (Est : List (List Nat))
    (El : List (List (List Nat))) (ms : List MovW) : Bool :=
  El.length == ms.length && (El.zip ms).all fun em =>
    !(em.1.all fun x => Est.all (ccomm x)) ||
      (decide (em.2.k < Hs.length) && starCheck T (Hs.getD em.2.k KData.dflt) Est em.1 em.2)

end CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core
