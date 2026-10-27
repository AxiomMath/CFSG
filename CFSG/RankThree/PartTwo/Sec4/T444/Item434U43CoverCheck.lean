module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43PairCheck

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.Quasithin.G2U

@[expose] def dependent9 (a b : List ℕ) : Bool := b == a || b == sq4 a

@[expose] def yTriple (n : ℕ) : List ℕ := (uY.getD n ([], [])).1

@[expose] def yWord (n : ℕ) : List ℕ := (uY.getD n ([], [])).2

@[expose] def yEls (n : ℕ) : List (List ℕ) :=
  [one4, uAt ((yTriple n).getD 0 0), sq4 (uAt ((yTriple n).getD 0 0))].flatMap fun x =>
    [one4, uAt ((yTriple n).getD 1 0), sq4 (uAt ((yTriple n).getD 1 0))].flatMap fun y =>
      [one4, uAt ((yTriple n).getD 2 0), sq4 (uAt ((yTriple n).getD 2 0))].map fun w =>
        mul4 (mul4 x y) w

@[expose] def yOK (n : ℕ) : Bool :=
  (yTriple n).length == 3 && (yTriple n).all (· < 729) && wordOK (yWord n) &&
  (List.range 3).all (fun i => (List.range 3).all fun j =>
    commutes4 (uAt ((yTriple n).getD i 0)) (uAt ((yTriple n).getD j 0))) &&
  (List.range 3).all (fun i => cube4 (uAt ((yTriple n).getD i 0)) == one4) &&
  distinctCheck (yEls n).toArray &&
  (yTriple n).all fun q => inRt (posOf (conjStep (wordPair (yWord n)) (uAt q)))

@[noinline, expose] def uYCheck : Bool :=
  uY.length == 13 && (List.range 13).all yOK

@[expose] def yCommArr : Array (Array Bool) :=
  (List.range 39).toArray.map fun m =>
    (List.range 729).toArray.map fun p =>
      commutes4 (uAt ((yTriple (m / 3)).getD (m % 3) 0)) (uAt p)

@[expose] def cover1 (els : Array (List ℕ)) : Bool :=
  (List.range 8).any fun t =>
    !(els.getD (t + 1) [] == one4) &&
      inRt (posOf (conjStep (convPairArr.getD (posOf (els.getD (t + 1) [])) (wordPair []))
        (els.getD (t + 1) [])))

@[expose] def cover2 (els : Array (List ℕ)) : Bool :=
  (List.range 13).any fun n => (List.range 3).all fun i =>
    (List.range 8).any fun t =>
      !(els.getD (t + 1) [] == one4) &&
        (yCommArr.getD (3 * n + i) #[]).getD (posOf (els.getD (t + 1) [])) false

@[expose] def coverOK (ia ib : ℕ) : Bool :=
  !(isOrd3Arr.getD ia false) || !(isOrd3Arr.getD ib false) ||
    !(commutes4 (uAt ia) (uAt ib)) || dependent9 (uAt ia) (uAt ib) ||
    cover1 (e9Elems (uAt ia) (uAt ib)) || cover2 (e9Elems (uAt ia) (uAt ib))

@[noinline, expose] def coverRow (ia : ℕ) : Bool :=
  (List.range 729).all fun ib => ib ≤ ia || coverOK ia ib

set_option compiler.extract_closed false in
@[noinline, expose] def uCoverCheck : Bool :=
  (List.range 729).all coverRow

@[expose] def liftEl (i : ℕ) : List ℕ := uAt (uLiftBasis.getD i 0)

@[expose] def liftMat (j k i : ℕ) : ℕ := ((uLiftM.getD j []).getD k []).getD i 0

@[expose] def liftRhs (j i : ℕ) : List ℕ :=
  mul4 (pow4 (liftEl 0) (liftMat j 0 i)) (mul4 (pow4 (liftEl 1) (liftMat j 1 i))
    (mul4 (pow4 (liftEl 2) (liftMat j 2 i)) (mul4 (pow4 (liftEl 3) (liftMat j 3 i)) one4)))

@[noinline, expose] def uLiftCheck : Bool :=
  uLiftBasis.length == 4 && uLiftG.length == 2 && uLiftM.length == 2 && uLiftG.all wordOK &&
    (List.range 2).all (fun j => (List.range 4).all fun k => (List.range 4).all fun i =>
      decide (liftMat j k i < 3)) &&
    (List.range 2).all fun j => (List.range 4).all fun i =>
      conjStep (wordPair (uLiftG.getD j [])) (liftEl i) == liftRhs j i

set_option compiler.extract_closed false in
@[noinline, expose] def uCoverAll : Bool :=
  uYCheck && uCoverCheck && uLiftCheck

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
