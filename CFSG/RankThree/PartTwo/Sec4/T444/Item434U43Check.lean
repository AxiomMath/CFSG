module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Data
public import CFSG.Quasithin.Background.G2UClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.Quasithin.G2U

@[expose] def addC (a b : ℕ) : ℕ := 3 * ((a / 3 + b / 3) % 3) + (a % 3 + b % 3) % 3

@[expose] def mulC (a b : ℕ) : ℕ :=
  3 * ((a / 3 * (b / 3) + 2 * (a % 3 * (b % 3))) % 3) + (a / 3 * (b % 3) + a % 3 * (b / 3)) % 3

@[expose] def cjC (a : ℕ) : ℕ := 3 * (a / 3 % 3) + (3 - a % 3) % 3

@[expose] def one4 : List ℕ := [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3]

@[expose] def mul4 (a b : List ℕ) : List ℕ :=
  let aa := a.toArray
  let bb := b.toArray
  (List.range 16).map fun k =>
    let i := k / 4
    let j := k % 4
    addC (addC (addC (mulC (aa.getD (4 * i) 0) (bb.getD j 0))
      (mulC (aa.getD (4 * i + 1) 0) (bb.getD (4 + j) 0)))
      (mulC (aa.getD (4 * i + 2) 0) (bb.getD (8 + j) 0)))
      (mulC (aa.getD (4 * i + 3) 0) (bb.getD (12 + j) 0))

@[expose] def adj4 (c : List ℕ) : List ℕ :=
  (List.range 16).map fun k => cjC (c.getD (4 * (k % 4) + k / 4) 0)

@[expose] def canon4 (c : List ℕ) : Bool :=
  c.length == 16 && c.all (· < 9)

@[expose] def sq4 (c : List ℕ) : List ℕ := mul4 c c

@[expose] def cube4 (c : List ℕ) : List ℕ := mul4 c (sq4 c)

@[expose] def pow4 (c : List ℕ) (k : ℕ) : List ℕ :=
  if k = 0 then one4 else if k = 1 then c else sq4 c

@[expose] def commutes4 (x y : List ℕ) : Bool := mul4 x y == mul4 y x

@[expose] def matAc : List ℕ := [2, 2, 5, 0, 2, 0, 5, 6, 8, 8, 2, 7, 0, 3, 4, 2]

@[expose] def matBc : List ℕ := [6, 4, 7, 7, 1, 6, 5, 0, 0, 4, 3, 2, 8, 4, 5, 3]

@[expose] def matAic : List ℕ := adj4 matAc

@[expose] def matBic : List ℕ := adj4 matBc

@[expose] def letterCode (l : ℕ) : List ℕ :=
  if l = 0 then matAc else if l = 1 then matBc else if l = 2 then matAic else matBic

@[expose] def wordCode (w : List ℕ) : List ℕ :=
  w.foldl (fun acc l => mul4 acc (letterCode l)) one4

@[expose] def invWord (w : List ℕ) : List ℕ :=
  (w.map fun l => if l < 2 then l + 2 else l - 2).reverse

@[expose] def wordPair (w : List ℕ) : List ℕ :=
  wordCode w ++ wordCode (invWord w)

@[expose] def conjStep (p : List ℕ) (x : List ℕ) : List ℕ :=
  mul4 (mul4 (p.take 16) x) (p.drop 16)

@[expose] def wordOK (w : List ℕ) : Bool := w.all (· < 4)

@[expose] def uGens : List (List ℕ) := uGenWords.map wordCode

@[expose] def uElems : Array (List ℕ) := build one4 mul4 uGens uPar

@[expose] def uAt (t : ℕ) : List ℕ := uElems.getD t []

set_option compiler.extract_closed false in
@[noinline, expose] def uSylCheck : Bool :=
  uElems.size == 729 && closedCheck mul4 uGens uElems && distinctCheck uElems &&
    allCheck canon4 uElems && uGenWords.all wordOK

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
