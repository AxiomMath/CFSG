module

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

@[expose] def N : Nat := 19683

@[expose] def vmDig (v b k : Nat) : Nat :=
  ((v % 3) * (((b % 27) / k) % 3) + ((v / 3) % 3) * ((((b / 27) % 27) / k) % 3) +
    ((v / 9) % 3) * ((((b / 729) % 27) / k) % 3)) % 3

@[expose] def vmRaw (v b : Nat) : Nat := vmDig v b 1 + 3 * vmDig v b 3 + 9 * vmDig v b 9

@[expose] def vmTab (_ : Unit := ()) : Array Nat :=
  Array.ofFn (n := 27 * 19683) fun k => vmRaw (k.1 / 19683) (k.1 % 19683)

@[expose] def act (T : Array Nat) (c r : Nat) : Nat := T[r * 19683 + c]!

@[expose] def mulc (T : Array Nat) (a b : Nat) : Nat :=
  act T b (a % 27) + 27 * act T b ((a / 27) % 27) + 729 * act T b ((a / 729) % 27)

@[expose] def oneC : Nat := 6643

@[expose] def negV (r : Nat) : Nat :=
  (2 * (r % 3)) % 3 + 3 * ((2 * ((r / 3) % 3)) % 3) + 9 * ((2 * ((r / 9) % 3)) % 3)

@[expose] def rawInv (c : Nat) : Bool :=
  let a0 := (c % 27) % 3
  let a1 := ((c % 27) / 3) % 3
  let a2 := ((c % 27) / 9) % 3
  let b0 := ((c / 27) % 27) % 3
  let b1 := (((c / 27) % 27) / 3) % 3
  let b2 := (((c / 27) % 27) / 9) % 3
  let c0 := ((c / 729) % 27) % 3
  let c1 := (((c / 729) % 27) / 3) % 3
  let c2 := (((c / 729) % 27) / 9) % 3
  (a0 * b1 * c2 + a1 * b2 * c0 + a2 * b0 * c1 +
    2 * (a0 * b2 * c1 + a1 * b0 * c2 + a2 * b1 * c0)) % 3 != 0

@[expose] def expand (T : Array Nat) (gens : List Nat) (x : Nat)
    (st : Array Nat × Array Bool) : Array Nat × Array Bool :=
  gens.foldl (fun (st : Array Nat × Array Bool) g =>
    let c := mulc T x g
    if st.2[c]! then st else (st.1.push c, st.2.set! c true)) st

@[expose] def bfsLoop (T : Array Nat) (gens : List Nat) :
    Nat → Nat → Array Nat × Array Bool → Array Nat × Array Bool
  | 0, _, st => st
  | fuel + 1, i, st =>
    if h : i < st.1.size then bfsLoop T gens fuel (i + 1) (expand T gens st.1[i] st) else st

@[expose] def bfs (T : Array Nat) (gens : List Nat) : Array Nat × Array Bool :=
  bfsLoop T gens 19683 0 (#[oneC], (Array.replicate 19683 false).set! oneC true)

structure Entry where
  gens : List Nat
  es : Array Nat
  seen : Array Bool
  deriving Inhabited

@[expose] def mkEntry (T : Array Nat) (gens : List Nat) : Entry :=
  ⟨gens, (bfs T gens).1, (bfs T gens).2⟩

@[expose] def mkEntries (T : Array Nat) (lat : List (List Nat)) : Array Entry :=
  (lat.map (mkEntry T)).toArray

@[expose] def minMul (T : Array Nat) (es : Array Nat) (x : Nat) : Nat :=
  es.foldl (fun b s => min b (mulc T s x)) x

@[expose] def repsOf (T : Array Nat) (U : Array Nat) (es : Array Nat) (seen : Array Bool) :
    Array Nat :=
  let mk := U.foldl (fun mk x => if seen[x]! then mk else mk.set! (minMul T es x) true)
    (Array.replicate 19683 false)
  (Array.range 19683).filter fun v => mk[v]!

@[expose] def entryOK (T : Array Nat) (U : Array Nat) (E : Array Entry) (j : Nat) : Bool :=
  let e := E[j]!
  e.gens.all (fun g => e.seen[g]!) &&
    (repsOf T U e.es e.seen).all fun g =>
      !(e.es.contains g) &&
        let D := bfs T (e.gens ++ [g])
        (List.range E.size).any fun j' =>
          let f := E[j']!
          f.es.size == D.1.size && f.es.all (fun c => D.2[c]!) && e.es.all (fun c => f.seen[c]!) &&
            f.seen[g]!

@[expose] def latCheck (T : Array Nat) (U : Array Nat) (E : Array Entry) : Bool :=
  (List.range E.size).all (entryOK T U E)

@[expose] def L1 : List (List Nat) :=
  [
    [], [13285], [6724], [6967], [7210], [2431], [13690], [11098], [13204], [17578], [15391],
    [4861], [8911], [13447], [7129], [15796], [8830], [2836], [18064], [11584], [4618],
    [6724, 13285], [6967, 13285], [7210, 13285], [13285, 15391], [13285, 17578], [13285, 2431],
    [7129, 13285], [15796, 13285], [8830, 13285], [2836, 13285], [7129, 6724], [15796, 2431],
    [8830, 13204], [2836, 4861], [7129, 13204], [15796, 4861], [8830, 6724], [2836, 2431],
    [2674, 18064], [2674, 6724], [9154, 6967], [15634, 7210], [17902], [11422], [4942],
    [7129, 6724, 13285], [15796, 13285, 2431], [8830, 13204, 13285], [2836, 13285, 4861],
    [2674, 18064, 6724], [9154, 11584, 6967], [15634, 4618, 7210], [2674, 18064, 7129],
    [7129, 15958]]

@[expose] def lat0 : List (List Nat) :=
  [
    [2674, 18064], [2674, 18064, 13286], [2674, 18064, 4862], [2674, 15634, 15392],
    [15634, 18064, 6968], [2674, 18064, 2431], [2674, 15634, 11098], [15634, 18064, 13690],
    [4618, 18064, 15796], [18064, 13286, 2431], [2674, 13286, 11098], [15634, 13690, 13286],
    [7129, 15553], [18064, 15796, 13286], [7129, 15554], [6130, 13069, 7399, 7426],
    [2674, 9154, 6655, 6664], [2675, 4780, 13690, 13286], [16418, 6130, 7426, 13286],
    [2674, 9154, 6664, 13286], [5645, 13042], [15392, 10639], [7751, 6130], [9154, 15413],
    [2432, 15649], [2674, 8924], [9154, 11113], [15634, 4864], [2674, 17602], [3214, 13096],
    [9181, 12583], [13690, 4672], [6889, 9154], [11017, 6130], [13295, 9154, 11098],
    [13295, 15634, 4861], [13295, 2674, 17578], [11611, 6670, 13286, 3214],
    [9937, 8155, 13286, 12583], [5374, 7372, 13690, 13286], [7129, 17930],
    [2674, 6655, 4780, 13286], [9910, 8128, 6265, 13286], [6886, 15967], [6886, 15977],
    [7129, 4915], [13796, 15958], [13529, 5618], [17572, 11123], [8792, 15403]]

@[expose] def lat1 : List (List Nat) :=
  [
    [2674, 6724], [2674, 18064, 2431], [2674, 9155, 2431], [6724, 13286, 2431],
    [18064, 13286, 2431], [7129, 15553], [6724, 13204, 13286, 18948], [6591, 13286, 2431, 4861],
    [5347, 7399, 7426, 5617], [4618, 6655, 6658, 4861], [2675, 4780, 13690, 13286], [3214, 16391],
    [4864, 11585], [15634, 4864], [4133, 7426, 13286, 3944], [13307, 4618, 4861], [3214, 13096],
    [13295, 15634, 4861], [11611, 6670, 13286, 3214], [6886, 15967], [7129, 4915], [13796, 15958],
    [13529, 5618], [8792, 15403]]

@[expose] def lat2 : List (List Nat) :=
  [
    [9154, 6967], [15634, 18064, 13690], [11585, 18064, 13690], [13690, 13286, 17578],
    [15634, 13690, 13286], [7129, 15553], [6967, 13690, 13286, 11694], [7086, 13286, 8911, 17578],
    [9937, 6697, 7426, 7021], [18064, 6664, 6649, 17578], [2675, 4780, 13690, 13286],
    [13690, 2702], [4619, 17602], [2674, 17602], [19550, 7426, 13286, 13718],
    [13289, 18064, 17578], [13690, 4672], [13295, 2674, 17578], [5374, 7372, 13690, 13286],
    [6886, 15967], [7129, 4915], [13796, 15958], [13529, 5618], [8792, 15403]]

@[expose] def lat3 : List (List Nat) :=
  [
    [15634, 7210], [2674, 15634, 11098], [15634, 4619, 11098], [13447, 13286, 11098],
    [2674, 13286, 11098], [7129, 15553], [7210, 13447, 13286, 5196], [6852, 13286, 15391, 11098],
    [13042, 7426, 8101, 16849], [11584, 6646, 6667, 11098], [2675, 4780, 13690, 13286],
    [18119, 12583], [11113, 18065], [9154, 11113], [16364, 7426, 13286, 11828],
    [13298, 11584, 11098], [9181, 12583], [13295, 9154, 11098], [9937, 8155, 13286, 12583],
    [6886, 15967], [7129, 4915], [13796, 15958], [13529, 5618], [8792, 15403]]

@[expose] def L2 : List (List (List Nat)) := [lat0, lat1, lat2, lat3]

@[expose] def tauC : Nat := 13285

@[expose] def inB (c : Nat) : Bool :=
  c % 27 == 1 && (c / 27) % 3 == 0 && (c / 729) % 3 == 0 && rawInv c

@[expose] def isQ (T : Array Nat) (es : Array Nat) : Bool :=
  es.size == 8 && es.contains tauC && es.any fun a => es.any fun b => mulc T a b != mulc T b a

@[expose] def stabArr (T : Array Nat) (S : Array Nat) : Array Nat :=
  S.filter fun c => act T c 1 == 1

@[expose] def hypB (T : Array Nat) (S : Array Nat) : Bool := (stabArr T S).size == 8

@[expose] def hypC (T : Array Nat) (S : Array Nat) : Bool :=
  (stabArr T S).any fun a => (stabArr T S).any fun b => mulc T a b != mulc T b a

@[expose] def hypD (T : Array Nat) (S : Array Nat) : Bool :=
  S.all fun c => !(act T c 1 == 1 || act T c 1 == 2) ||
    (act T c 3 % 3 == 0 && act T c 9 % 3 == 0 &&
      (stabArr T S).any fun d => (act T c 3 == act T d 3 && act T c 9 == act T d 9) ||
        (act T c 3 == negV (act T d 3) && act T c 9 == negV (act T d 9)))

@[expose] def hypE (T : Array Nat) (S : Array Nat) : Bool :=
  S.any fun c => act T c 1 != 1 && act T c 1 != 2

@[expose] def phiHyp (T : Array Nat) (S : Array Nat) : Bool :=
  hypB T S && hypC T S && hypD T S && hypE T S

@[expose] def phiC1 (T : Array Nat) (S : Array Nat) : Bool :=
  (S.all fun c => act T c 3 % 3 == 0 && act T c 9 % 3 == 0) &&
    (List.range 27).all fun u => u % 3 == 0 ||
      S.any fun c => act T c 1 == u || act T c 1 == negV u

@[expose] def phiC2 (T : Array Nat) (S : Array Nat) : Bool :=
  (List.range 27).any fun u1 => u1 % 3 == 0 &&
    (List.range 27).any fun u2 => u2 % 3 == 0 &&
      ((u1 / 3) % 3 * ((u2 / 9) % 3) + 2 * ((u1 / 9) % 3 * ((u2 / 3) % 3))) % 3 != 0 &&
      (S.all fun c => [1, 2, u1, negV u1, u2, negV u2].all fun x =>
        act T c x == 1 || act T c x == 2 || act T c x == u1 || act T c x == negV u1 ||
          act T c x == u2 || act T c x == negV u2) &&
      (S.any fun c => act T c 1 == 2 && act T c u1 == u1 && act T c u2 == u2) &&
      (S.any fun c => act T c 1 == u1 && act T c u1 == 1 && act T c u2 == u2) &&
      (S.any fun c => act T c 1 == u1 && act T c u1 == u2 && act T c u2 == 1)

@[expose] def phi (T : Array Nat) (S : Array Nat) : Bool :=
  !(phiHyp T S) || phiC1 T S || phiC2 T S

@[expose] def stage2 (T : Array Nat) (U2 : Array Nat) (qg : List Nat) (lat : List (List Nat)) :
    Bool :=
  lat.head? == some qg &&
    let E2 := mkEntries T lat
    latCheck T U2 E2 && E2.all fun e => phi T e.es

@[expose] def gl33CheckWith (T : Array Nat) : Bool :=
  let U1 := (Array.range 19683).filter inB
  let U2 := (Array.range 19683).filter rawInv
  let E1 := mkEntries T L1
  L1.head? == some [] && latCheck T U1 E1 &&
    E1.all fun e => !(isQ T e.es) ||
      L2.any fun lat => lat.head? == some e.gens && stage2 T U2 e.gens lat

@[expose] def gl33Check (_ : Unit := ()) : Bool := gl33CheckWith (vmTab ())

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
