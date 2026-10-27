module

public import Certificates.Data.S5RowsG23

public section

namespace Certificates.S7G23Insp

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U Certificates.S5RowsG23

@[expose] def es (i : ℕ) : List ℕ := elemsS.getD i []

@[expose] def k1s : List ℕ := [0, 1, 2, 6, 7, 11, 23, 24]

@[expose] def k2s : List ℕ := [0, 3, 4, 6, 15, 17, 25, 26]

@[expose] def wordG (_ : Unit := ()) : List (List ℕ) :=
  [x0c, x1c, x0c, y0c, sq14 y1c, y0c, y1c, x1c, sq14 x0c, y0c]

@[expose] def gc (_ : Unit := ()) : List ℕ := (wordG ()).foldl mul14 one14

@[expose] def gic (_ : Unit := ()) : List ℕ :=
  (wordG ()).reverse.foldl (fun a w => mul14 a (sq14 w)) one14

@[expose] def closedL (ks : List ℕ) : Bool :=
  ks.all fun a => ks.all fun b => ks.any fun c => mul14 (es a) (es b) == es c

@[expose] def c0 (_ : Unit := ()) : Bool :=
  closedL k1s && closedL k2s && q8RelC (es 1) (es 2) && q8RelC (es 3) (es 4) &&
    sq14 (es 1) == tc && sq14 (es 3) == tc && !(k2s.any fun b => es b == es 1) &&
    (k1s ++ k2s).all (· < elemsS.size)

@[expose] def c1 (_ : Unit := ()) : Bool :=
  (List.range 64).all fun a => (List.range 64).all fun b =>
    !q8RelC (es a) (es b) || (k1s.contains a && k1s.contains b) || (k2s.contains a && k2s.contains b)

@[expose] def c2 (_ : Unit := ()) : Bool :=
  [k1s, k2s].all fun ks => gensX.all fun y => ks.all fun k => ks.any fun k' =>
    mul14 y (es k) == mul14 (es k') y

@[expose] def c3 (_ : Unit := ()) : Bool :=
  let g := gc (); let gi := gic ()
  mul14 g gi == one14 &&
    (sq14 (es 4) != one14 && sq14 (sq14 (es 4)) == one14 &&
      elemsX.contains (mul14 (mul14 g (es 4)) gi)) &&
    !elemsX.contains (mul14 (mul14 g (es 25)) gi)

@[expose] def c4 (_ : Unit := ()) : Bool :=
  let g2 := sq14 (gc ()); let gi2 := sq14 (gic ())
  x0c == mul14 (mul14 g2 (sq14 vc)) gi2 && y0c == mul14 (mul14 gi2 uc) g2

end Certificates.S7G23Insp
