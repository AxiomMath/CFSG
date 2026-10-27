module

public section

namespace CFSG.GMS78Ru

abbrev V3 : Type := Fin 8 × Fin 8 × Fin 8

@[expose] def mulTab : Array (Fin 8) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7,
  0, 2, 4, 6, 3, 1, 7, 5, 0, 3, 6, 5, 7, 4, 1, 2, 0, 4, 3, 7, 6, 2, 5, 1, 0, 5, 1, 4, 2, 7, 3, 6,
  0, 6, 7, 1, 5, 3, 2, 4, 0, 7, 5, 2, 1, 6, 4, 3]

@[expose, inline] def mul8 (a b : Fin 8) : Fin 8 := mulTab.getD (8 * a.val + b.val) 0

@[expose] def addV (x y : V3) : V3 := (x.1 ^^^ y.1, x.2.1 ^^^ y.2.1, x.2.2 ^^^ y.2.2)

@[expose, inline] def sqN (c e : Fin 8) (x : V3) : Fin 8 :=
  let u2 := mul8 x.1 x.1
  let ur := mul8 x.1 x.2.1
  mul8 (mul8 u2 u2) x.1 ^^^ mul8 c (mul8 ur ur) ^^^ mul8 (e ^^^ x.2.2) x.2.1

@[expose, inline] def commN (c : Fin 8) (x z : V3) : Fin 8 :=
  let x2 := mul8 x.1 x.1
  let z2 := mul8 z.1 z.1
  let a := mul8 x.1 z.2.1
  let b := mul8 z.1 x.2.1
  mul8 x.1 (mul8 z2 z2) ^^^ mul8 (mul8 x2 x2) z.1 ^^^ mul8 c (mul8 a a ^^^ mul8 b b) ^^^
    mul8 x.2.2 z.2.1 ^^^ mul8 z.2.2 x.2.1

@[expose] def all8 : List (Fin 8) := List.finRange 8

@[expose] def lamList (p q : Fin 8) : List (Fin 8) := [0, p, q, p ^^^ q]

@[expose] def wList (p q : Fin 8) : List V3 :=
  all8.flatMap fun u => all8.flatMap fun r => (lamList p q).map fun s => (u, r, s)

@[expose] def canon (p q : Fin 8) : Bool :=
  decide (0 < p.val) && decide (p.val < q.val) && decide (q.val < (p ^^^ q).val)

@[expose] def indep3 (a b c : Fin 8) : Bool :=
  a != 0 && b != 0 && b != a && c != 0 && c != a && c != b && c != (a ^^^ b)

@[expose] def spanAt (c e : Fin 8) (W : List V3) (x : V3) : Bool :=
  W.any fun z₁ => commN c x z₁ == 0 &&
    (let q₁ := sqN c e z₁
     q₁ != 0 && W.any fun z₂ => commN c x z₂ == 0 &&
       (let q₂ := sqN c e z₂
        q₂ != 0 && q₂ != q₁ && W.any fun z₃ => commN c x z₃ == 0 && indep3 q₁ q₂ (sqN c e z₃)))

@[expose] def c1Check : Bool :=
  all8.all fun c => c == 0 || all8.all fun e => all8.all fun p => all8.all fun q =>
    !canon p q || (let W := wList p q
      W.all fun x => x.1 == 0 || x.2.1 == 0 || sqN c e x != 0 || spanAt c e W x)

@[expose] def allNZ (x : V3) : Bool := x.1 != 0 && x.2.1 != 0 && x.2.2 != 0

@[expose] def lineList (p q : Fin 8) : List V3 :=
  (all8.map fun u => (u, 0, 0)) ++ (all8.map fun r => (0, r, 0)) ++
    ((lamList p q).map fun s => (0, 0, s))

@[expose] def specialList : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) :=
  [(7, 5, 1, 2), (3, 7, 1, 4), (5, 3, 1, 6), (1, 1, 2, 4), (2, 6, 2, 5), (4, 2, 3, 4), (6, 4, 3, 5)]

@[expose] def c2Check : Bool :=
  all8.all fun c => c == 0 || all8.all fun e => all8.all fun p => all8.all fun q =>
    !canon p q || specialList.contains (c, e, p, q) ||
      (let zs := (wList p q).filter fun x => allNZ x && sqN c e x == 0
       let ls := lineList p q
       zs.all fun x => zs.all fun y => x == y || commN c x y != 0 || !allNZ (addV x y) ||
         !(ls.all fun z => (commN c x z == 0) == (commN c y z == 0)))

@[expose] def basisList (p q : Fin 8) : List V3 :=
  [(1, 0, 0), (0, 1, 0), (0, 0, p), (2, 0, 0), (0, 2, 0), (0, 0, q), (4, 0, 0), (0, 4, 0)]

@[expose] def candTab (c e : Fin 8) (W : List V3) : List (List V3) :=
  all8.map fun t => W.filter fun w => sqN c e w == t

@[expose] def isoExt (tab : List (List V3)) (c e : Fin 8) : List V3 → List (V3 × V3) → Bool
  | [], done => done.all fun pr => pr.1 == pr.2
  | b :: bs, done =>
    let tgt := done.map fun pr => (pr.2, commN c pr.1 b)
    (tab.getD (sqN c e b).val []).all fun w =>
      !(tgt.all fun pr => commN c pr.1 w == pr.2) || isoExt tab c e bs ((b, w) :: done)

@[expose] def c3Check : Bool :=
  all8.all fun c => all8.all fun e => all8.all fun p => all8.all fun q =>
    !canon p q || isoExt (candTab c e (wList p q)) c e (basisList p q) []

end CFSG.GMS78Ru
