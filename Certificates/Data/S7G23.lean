module

public import Certificates.Data.S5RowsG23

public section

namespace Certificates.S7G23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three Certificates.S5RowsG23

@[expose] def gensC : List (List ℕ) := [x0c, x1c, y0c, y1c]

@[expose] def wordC (w : List ℕ) : List ℕ :=
  w.foldl (fun acc k => mul14 acc (gensC.getD k one14)) one14

@[expose] def wordInvC (w : List ℕ) : List ℕ :=
  w.reverse.foldl (fun acc k => mul14 acc (sq14 (gensC.getD k one14))) one14

@[expose] def spanC (i j : List ℕ) : List (List ℕ) :=
  let i2 := sq14 i
  let j2 := sq14 j
  [one14, i2, i, mul14 i2 i, j, mul14 j2 j, mul14 i j, mul14 j i]

@[expose] def inSpanC (i j x : List ℕ) : Bool :=
  (spanC i j).contains x

@[expose] def conjInC (sp : List (List ℕ)) (g x : List ℕ) : Bool :=
  let gx := mul14 g x
  sp.any fun q => gx == mul14 q g

@[expose] def normC (i j g : List ℕ) : Bool :=
  let sp := spanC i j
  conjInC sp g i && conjInC sp g j

@[expose] def ord4C (u : List ℕ) : Bool :=
  let u2 := sq14 u
  sq14 u2 == one14 && !(u2 == one14)

@[expose] def normVC (z w a : List ℕ) : Bool :=
  let V := [one14, z, w, mul14 z w]
  conjInC V a z && conjInC V a w

@[expose] def classStepC (i j u xw : List ℕ) : Bool :=
  let x := wordC xw
  let xi := wordInvC xw
  let z := sq14 i
  let w := sq14 u
  let i' := mul14 (mul14 x i) xi
  let j' := mul14 (mul14 x j) xi
  let sp := spanC i' j'
  (mul14 x xi == one14) && (mul14 x z == mul14 w x) &&
    (!(inSpanC i' j' u && !(inSpanC i j i' && inSpanC i j j') &&
        !(normC i j i' && normC i j j')) ||
      (spanC i j).any fun a => sp.any fun b =>
        normVC z w a && normVC z w b && conjInC sp (mul14 a b) i && conjInC sp (mul14 a b) j)

@[expose] def classCheckC (i j : List ℕ) (S X : List (List ℕ)) : Bool :=
  S.all fun u => !ord4C u || X.any fun xw => classStepC i j u xw

@[expose] def normAllC (i j : List ℕ) (C : List (List ℕ)) : Bool :=
  C.all fun c => normC i j c

@[expose] def q8InCheckC (L : List (List ℕ)) (i₁ j₁ i₂ j₂ : List ℕ) : Bool :=
  let o4 := (L.filter ord4C).map fun a => (a, sq14 a)
  o4.all fun a => o4.all fun b => !(a.2 == b.2 && mul14 (mul14 a.1 b.1) a.1 == b.1) ||
    (inSpanC i₁ j₁ a.1 && inSpanC i₁ j₁ b.1) || (inSpanC i₂ j₂ a.1 && inSpanC i₂ j₂ b.1)

@[expose] def i1W : List ℕ := [1, 3, 3, 1]

@[expose] def j1W : List ℕ := [1, 1, 3, 3, 1, 1, 1]

@[expose] def i2W : List ℕ :=
  [0, 2, 2, 0, 1, 3, 3, 1, 0, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1, 3,
   3, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 3, 1, 2, 1, 1, 3,
   3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 3, 1, 0, 1, 1, 3, 3, 3, 3, 1, 1, 0,
   0, 2, 2, 2, 2, 0, 0]

@[expose] def j2W : List ℕ :=
  [0, 2, 2, 0, 1, 3, 3, 1, 0, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1, 3,
   3, 1, 0, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 3, 1, 2, 1, 1, 3,
   3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 0,
   0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 3, 1, 0, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0,
   0, 0, 2, 2, 0, 1, 3, 3, 1, 0, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 1,
   3, 3, 1, 0, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0, 2, 2, 2, 2, 0, 0]

@[expose] def i1 : List ℕ := wordC i1W

@[expose] def j1 : List ℕ := wordC j1W

@[expose] def i2 : List ℕ := wordC i2W

@[expose] def j2 : List ℕ := wordC j2W

@[expose] def conjW : List (List ℕ) :=
  [[2, 1, 0, 1, 3, 2, 0, 1, 1, 3, 2, 0, 0], [3, 0, 2, 2, 3, 2, 3, 2, 1, 0, 1, 0, 0], []]

@[expose] def g23S7Basic (_ : Unit := ()) : Bool :=
  q8RelC i1 j1 && q8RelC i2 j2 && sq14 i1 == tc && sq14 i2 == tc && !inSpanC i1 j1 i2

@[expose] def g23S7Class1 (_ : Unit := ()) : Bool :=
  classCheckC i1 j1 elemsS.toList conjW

@[expose] def g23S7Class2 (_ : Unit := ()) : Bool :=
  classCheckC i2 j2 elemsS.toList conjW

@[expose] def g23S7Norm (_ : Unit := ()) : Bool :=
  let x := elemsX.toList
  let s := elemsS.toList
  normAllC i1 j1 x && normAllC i2 j2 x && normAllC i1 j1 s && normAllC i2 j2 s

@[expose] def g23S7Q8 (_ : Unit := ()) : Bool :=
  q8InCheckC elemsS.toList i1 j1 i2 j2

end Certificates.S7G23
