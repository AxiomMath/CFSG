module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Data

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemG23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U

@[expose] def letterCode (l : ℕ) : List ℕ :=
  if l < 4 then [x0c, x1c, y0c, y1c].getD l one14
  else sq14 ([x0c, x1c, y0c, y1c].getD (l - 4) one14)

@[expose] def wordCode (w : List ℕ) : List ℕ :=
  w.foldl (fun acc l => mul14 acc (letterCode l)) one14

@[expose] def invWord (w : List ℕ) : List ℕ :=
  (w.map fun l => if l < 4 then l + 4 else l - 4).reverse

@[expose] def wordPair (w : List ℕ) : List ℕ :=
  wordCode w ++ wordCode (invWord w)

@[expose] def cube14 (c : List ℕ) : List ℕ :=
  mul14 c (sq14 c)

@[expose] def pow14 (c : List ℕ) (k : ℕ) : List ℕ :=
  if k = 0 then one14 else if k = 1 then c else sq14 c

@[expose] def sylGens : List (List ℕ) :=
  [x0c, x1c, wordCode sylWord]

@[expose] def sylElems : Array (List ℕ) :=
  build one14 mul14 sylGens sylPar

@[expose] def sylAt (t : ℕ) : List ℕ :=
  sylElems.getD t []

set_option compiler.extract_closed false in
@[noinline, expose] def sylCheck : Bool :=
  sylElems.size == 729 && closedCheck mul14 sylGens sylElems && distinctCheck sylElems &&
    allCheck canon14 sylElems && [x0c, x1c, y0c, y1c].all fun c => cube14 c == one14

@[expose] def dEl (D : List ℕ) (j : ℕ) : List ℕ :=
  sylAt (D.getD j 0)

@[expose] def dProd (D : List ℕ) (u : ℕ) : List ℕ :=
  mul14 (mul14 (mul14 (pow14 (dEl D 0) (u % 3)) (pow14 (dEl D 1) (u / 3 % 3)))
    (pow14 (dEl D 2) (u / 9 % 3))) (pow14 (dEl D 3) (u / 27 % 3))

@[expose] def dArr (D : List ℕ) : Array (List ℕ) :=
  ((List.range 81).map (dProd D)).toArray

@[expose] def dOK (D : List ℕ) : Bool :=
  D.length == 4 && D.all (· < 729) &&
    (List.range 4).all (fun a => (List.range 4).all fun b => commutes (dEl D a) (dEl D b)) &&
    (List.range 4).all (fun a => cube14 (dEl D a) == one14) &&
    distinctCheck (dArr D) && found (dArr D) (indexMap (dArr D)) (sylAt sylZIdx)

@[expose] def zOK : Bool :=
  sylZ.all (fun i => decide (i < 729) && sylGens.all (commutes (sylAt i))) &&
    decide (sylZIdx < 729) && sylGens.all (commutes (sylAt sylZIdx)) &&
    cube14 (sylAt sylZIdx) == one14 && !(sylAt sylZIdx == one14)

@[expose] def coverK2 : Bool :=
  let maps := sylDs.map fun D => (dArr D, indexMap (dArr D))
  (List.range 729).all fun t =>
    let c := sylAt t
    c == one14 || !(cube14 c == one14) || maps.any fun p => found p.1 p.2 c

set_option compiler.extract_closed false in
@[noinline, expose] def k2Check : Bool :=
  zOK && sylDs.all dOK && coverK2

@[expose] def zCodes : List (List ℕ) :=
  sylZ.map sylAt

@[expose] def tCodes : List (List ℕ) :=
  conjWords.flatMap fun w => zCodes.map fun zc => conjStep (wordPair (invWord w)) zc

@[expose] def isTIdx (t : ℕ) : Bool :=
  tCodes.contains (sylAt t)

@[expose] def tArr : Array Bool :=
  ((List.range 729).map isTIdx).toArray

@[expose] def isN (t : ℕ) : Bool :=
  !(sylAt t == one14) && cube14 (sylAt t) == one14 && !(tArr.getD t false)

@[expose] def rtIdx (m : Std.HashMap (List ℕ) ℕ) (i s : ℕ) : ℕ :=
  (m.get? (mul14 (sylAt i) (sylGens.getD s one14))).getD 0

@[expose] def rtTab (m : Std.HashMap (List ℕ) ℕ) : Array (Array ℕ) :=
  ((List.range 729).map fun i => ((List.range 3).map (rtIdx m i)).toArray).toArray

@[expose] def rtStep (rt : Array (Array ℕ)) (i s : ℕ) : ℕ :=
  (rt.getD i #[]).getD s 0

@[expose] def pathsArr : Array (List ℕ) :=
  sylPar.foldl (fun acc ps => acc.push (acc.getD ps.1 [] ++ [ps.2])) #[[]]

@[expose] def mulIdx (rt : Array (Array ℕ)) (a b : ℕ) : ℕ :=
  (pathsArr.getD b []).foldl (rtStep rt) a

@[expose] def rtOK (m : Std.HashMap (List ℕ) ℕ) : Bool :=
  (List.range 729).all fun i => (List.range 3).all fun s =>
    found sylElems m (mul14 (sylAt i) (sylGens.getD s one14))

@[expose] def pathOK (rt : Array (Array ℕ)) : Bool :=
  (List.range 729).all fun k =>
    (pathsArr.getD k []).all (· < 3) && (pathsArr.getD k []).foldl (rtStep rt) 0 == k

@[expose] def wordsOK : Bool :=
  sylWord.all (· < 8) && conjWords.all (·.all (· < 8)) && liftG.all (·.all (· < 8))

@[expose] def rtMain : Array (Array ℕ) :=
  rtTab (indexMap sylElems)

@[expose] def nArr : Array Bool :=
  ((List.range 729).map isN).toArray

set_option compiler.extract_closed false in
@[noinline, expose] def coverLoop : Bool :=
  (List.range 729).all fun ia => !(nArr.getD ia false) ||
    (let aa := mulIdx rtMain ia ia
     (List.range 729).all fun ib => !(nArr.getD ib false) ||
       (ib == ia || ib == aa || !(mulIdx rtMain ia ib == mulIdx rtMain ib ia) ||
        tArr.getD (mulIdx rtMain ia ib) false ||
        tArr.getD (mulIdx rtMain (mulIdx rtMain ia ib) ib) false))

set_option compiler.extract_closed false in
@[noinline, expose] def coverCheck : Bool :=
  wordsOK && rtOK (indexMap sylElems) && pathOK rtMain && coverLoop

@[expose] def liftEl (i : ℕ) : List ℕ :=
  sylAt (liftW.getD i 0)

@[expose] def liftProd (u : ℕ) : List ℕ :=
  mul14 (mul14 (pow14 (liftEl 0) (u % 3)) (pow14 (liftEl 1) (u / 3 % 3)))
    (pow14 (liftEl 2) (u / 9 % 3))

@[expose] def liftMat (j k i : ℕ) : ℕ :=
  ((liftM.getD j []).getD k []).getD i 0

@[expose] def liftRhs (j i : ℕ) : List ℕ :=
  mul14 (pow14 (liftEl 0) (liftMat j 0 i)) (mul14 (pow14 (liftEl 1) (liftMat j 1 i))
    (mul14 (pow14 (liftEl 2) (liftMat j 2 i)) one14))

set_option compiler.extract_closed false in
@[noinline, expose] def liftCheck : Bool :=
  liftW.length == 3 && liftW.all (· < 729) && liftG.length == 2 && liftM.length == 2 &&
    (List.range 3).all (fun a => (List.range 3).all fun b => commutes (liftEl a) (liftEl b)) &&
    (List.range 3).all (fun a => cube14 (liftEl a) == one14) &&
    distinctCheck ((List.range 27).map liftProd).toArray &&
    (List.range 2).all (fun j => (List.range 3).all fun k => (List.range 3).all fun i =>
      decide (liftMat j k i < 3)) &&
    (List.range 2).all fun j => (List.range 3).all fun i =>
      conjStep (wordPair (liftG.getD j [])) (liftEl i) == liftRhs j i

end CFSG.RankThree.PartTwo.Sec4.Item434RemG23
