module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43ClassCheck

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.Quasithin.G2U

@[expose] def zc : List ℕ := uAt uZ

@[expose] def zc2 : List ℕ := sq4 zc

@[expose] def kindOf (c : List ℕ) : ℕ := kindAt (posOf c)

@[expose] def zaList (a : List ℕ) : List (List ℕ) :=
  [one4, zc, zc2].flatMap fun x => [one4, a, sq4 a].map fun y => mul4 x y

@[expose] def pElemsOf (za : List (List ℕ)) (b : List ℕ) : Array (List ℕ) :=
  (za.flatMap fun u => [u, mul4 u b, mul4 u (sq4 b)]).toArray

@[expose] def e9Elems (a b : List ℕ) : Array (List ℕ) :=
  ([one4, a, sq4 a].flatMap fun x => [one4, b, sq4 b].map fun y => mul4 x y).toArray

@[expose] def convPairArr : Array (List ℕ) :=
  (List.range 729).toArray.map fun p => wordPair (convRWord p)

@[expose] def dependent (a : List ℕ) (za : List (List ℕ)) (b : List ℕ) : Bool :=
  a == zc || a == zc2 || za.contains b

@[expose] def badTriple (k : ℕ) : List ℕ := (uBad.getD k (0, [], [])).2.1

@[expose] def badClass (k : ℕ) : ℕ := (uBad.getD k (0, [], [])).1

@[expose] def badWord (k : ℕ) : List ℕ := (uBad.getD k (0, [], [])).2.2

@[expose] def badA (k : ℕ) : List ℕ := uAt ((badTriple k).getD 1 0)

@[expose] def badB (k : ℕ) : List ℕ := uAt ((badTriple k).getD 2 0)

@[expose] def repIdx (c : ℕ) : ℕ := (uBad.findIdx fun e => e.1 == c)

@[expose] def badOK (k : ℕ) : Bool :=
  (badTriple k).length == 3 && (badTriple k).all (· < 729) && (badTriple k).getD 0 0 == uZ &&
  repIdx (badClass k) < 12 &&
  commutes4 (badA k) (badB k) && cube4 (badA k) == one4 && cube4 (badB k) == one4 &&
  !(badA k == one4) && !([one4, badA k, sq4 (badA k)].contains (badB k)) &&
  (e9Elems (badA k) (badB k)).all (fun c => c == one4 || kindOf c == 3) &&
  wordOK (badWord k) &&
  conjStep (wordPair (badWord k)) (badA k) == badA (repIdx (badClass k)) &&
  conjStep (wordPair (badWord k)) (badB k) == badB (repIdx (badClass k)) &&
  (conjStep (wordPair (badWord k)) zc == zc || conjStep (wordPair (badWord k)) zc == zc2)

@[noinline, expose] def uBadCheck : Bool :=
  uBad.length == 12 && (List.range 12).all badOK

@[expose] def pairBad (els : Array (List ℕ)) : Bool :=
  (List.range 12).any fun k => els.contains (badA k) && els.contains (badB k)

@[expose] def pairGoodAt (els : Array (List ℕ)) (x : ℕ) : Bool :=
  let gp := convPairArr.getD (posOf (els.getD x [])) (wordPair [])
  (List.range 27).any fun u => !(els.getD u [] == one4) &&
    inRt (posOf (conjStep gp (els.getD u []))) &&
      (List.range 27).any fun v => !(els.getD v [] == one4) &&
        !(els.getD v [] == els.getD u []) && !(els.getD v [] == sq4 (els.getD u [])) &&
        inRt (posOf (conjStep gp (els.getD v [])))

@[expose] def pairGood (els : Array (List ℕ)) : Bool :=
  match (List.range 27).find? (fun e => e != 0 && kindOf (els.getD e []) == 2) with
  | none => false
  | some x => pairGoodAt els x

@[expose] def pairOKE (a b : List ℕ) : Bool :=
  let za := zaList a
  dependent a za b || (let els := pElemsOf za b; pairGood els || pairBad els)

@[expose] def isOrd3 (p : ℕ) : Bool := !(uAt p == one4) && cube4 (uAt p) == one4

@[expose] def isOrd3Arr : Array Bool := (List.range 729).toArray.map isOrd3

@[expose] def pairOK (ia ib : ℕ) : Bool :=
  !(isOrd3Arr.getD ia false) || !(isOrd3Arr.getD ib false) ||
    !(commutes4 (uAt ia) (uAt ib)) || pairOKE (uAt ia) (uAt ib)

@[noinline, expose] def pairRow (ia : ℕ) : Bool :=
  (List.range 729).all fun ib => ib ≤ ia || pairOK ia ib

set_option compiler.extract_closed false in
@[noinline, expose] def uPairCheck : Bool :=
  (List.range 729).all pairRow

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
