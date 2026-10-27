module

public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def full : Nat := 16777215

@[expose] def img (t : Array Nat) (m : Nat) : Nat :=
  (List.range 24).foldl (fun acc i => if m.testBit i then acc ||| (1 <<< t[i]!) else acc) 0

@[expose] def pop (m : Nat) : Nat :=
  (List.range 24).foldl (fun acc i => if m.testBit i then acc + 1 else acc) 0

@[expose] def syndCols : List Nat :=
  [62, 129, 65, 193, 61, 514, 258, 770, 59, 2052, 1028, 3076, 55, 2696, 1352, 4040, 47, 2896,
    1744, 3472, 31, 2528, 1952, 3680]

@[expose] def actM : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, m => (if m % 2 = 1 then c else 0) ^^^ actM cs (m / 2)

@[expose] def synd (m : Nat) : Nat := actM syndCols m

@[expose] def pATab : Array Nat :=
  #[3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]

@[expose] def pBTab : Array Nat :=
  #[3, 9, 6, 18, 4, 5, 13, 22, 8, 14, 10, 23, 15, 2, 1, 20, 16, 7, 0, 11, 12, 21, 17, 19]

@[expose] def pBiTab : Array Nat :=
  #[18, 14, 13, 0, 4, 5, 2, 17, 8, 1, 10, 19, 20, 6, 9, 12, 16, 22, 3, 23, 15, 21, 7, 11]

@[expose] def genTabs : List (Array Nat) := [pATab, pBTab, pBiTab]

@[expose] def lTabs : List (Array Nat) :=
  [#[12, 11, 8, 15, 10, 13, 14, 9, 19, 20, 23, 16, 21, 18, 17, 22, 1, 6, 5, 2, 7, 0, 3, 4],
    #[3, 4, 2, 5, 6, 1, 7, 0, 14, 9, 15, 8, 11, 12, 10, 13, 22, 17, 23, 16, 19, 20, 18, 21],
    #[15, 9, 8, 14, 13, 11, 10, 12, 3, 5, 4, 2, 1, 7, 6, 0, 22, 16, 17, 23, 20, 18, 19, 21],
    #[10, 9, 15, 12, 13, 14, 8, 11, 17, 18, 20, 23, 22, 21, 19, 16, 1, 2, 4, 7, 6, 5, 3, 0]]

@[expose] def uTabs : List (Array Nat) :=
  [#[18, 16, 19, 17, 15, 14, 12, 13, 4, 5, 7, 6, 21, 22, 23, 20, 8, 11, 10, 9, 3, 1, 2, 0],
    #[22, 21, 20, 23, 1, 2, 3, 0, 19, 16, 17, 18, 4, 7, 6, 5, 13, 12, 14, 15, 8, 10, 9, 11],
    #[5, 4, 7, 6, 20, 21, 22, 23, 3, 2, 1, 0, 18, 19, 16, 17, 12, 15, 13, 14, 10, 8, 9, 11],
    #[0, 2, 1, 3, 18, 16, 19, 17, 5, 7, 4, 6, 23, 21, 22, 20, 8, 11, 10, 9, 13, 12, 14, 15]]

@[expose] def bfs {α : Type} [Inhabited α] (key : α → Nat) (steps : List (α → α)) (base : α)
    (fuel : Nat) : Array α × Array Nat × Array Nat := Id.run do
  let mut list : Array α := #[base]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (key base) 0
  let mut h := 0
  for _ in [0:fuel] do
    if h < list.size then
      let x := list[h]!
      let mut j := 0
      for s in steps do
        let y := s x
        if !(seen.contains (key y)) then
          seen := seen.insert (key y) list.size
          list := list.push y
          par := par.push h
          gen := gen.push j
        j := j + 1
      h := h + 1
    else
      break
  return (list, par, gen)

@[expose] def indexMap {α : Type} [Inhabited α] (key : α → Nat) (l : Array α) :
    Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:l.size] do
    m := m.insert (key l[i]!) i
  return m

@[expose] def octData (_ : Unit := ()) : Array Nat × Array Nat × Array Nat :=
  bfs id (genTabs.map img) 255 1000

@[expose] def octList (_ : Unit := ()) : Array Nat := (octData ()).1

@[expose] def nOct : Nat := 759

@[expose] def octMap (_ : Unit := ()) : Std.HashMap Nat Nat := indexMap id (octList ())

@[expose] def octIdx (m : Nat) : Nat :=
  match (octMap ())[m]? with
  | some q => if q < nOct && (octList ())[q]! == m then q else nOct
  | none => nOct

@[expose] def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  if a ≤ b then
    if b ≤ c then (a, b, c) else if a ≤ c then (a, c, b) else (c, a, b)
  else
    if a ≤ c then (b, a, c) else if b ≤ c then (b, c, a) else (c, b, a)

@[expose] def key3 (t : Nat × Nat × Nat) : Nat := (t.1 <<< 48) ||| (t.2.1 <<< 24) ||| t.2.2

@[expose] def imgTrio (g : Array Nat) (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  sort3 (img g t.1) (img g t.2.1) (img g t.2.2)

@[expose] def baseTrio : Nat × Nat × Nat := (255, 65280, 16711680)

@[expose] def trioData (_ : Unit := ()) : Array (Nat × Nat × Nat) × Array Nat × Array Nat :=
  bfs key3 (genTabs.map imgTrio) baseTrio 5000

@[expose] def trioList (_ : Unit := ()) : Array (Nat × Nat × Nat) := (trioData ()).1

@[expose] def nTrio : Nat := 3795

@[expose] def trioMap (_ : Unit := ()) : Std.HashMap Nat Nat := indexMap key3 (trioList ())

@[expose] def trioIdx (t : Nat × Nat × Nat) : Nat :=
  match (trioMap ())[key3 t]? with
  | some q => if q < nTrio && (trioList ())[q]! == t then q else nTrio
  | none => nTrio

@[expose] def sortL (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

@[expose] def keyL (l : List Nat) : Nat := l.foldl (fun acc m => (acc <<< 24) ||| m) 0

@[expose] def imgSext (g : Array Nat) (s : List Nat) : List Nat := sortL (s.map (img g))

@[expose] def baseSext : List Nat := [15, 240, 3840, 61440, 983040, 15728640]

@[expose] def sextData (_ : Unit := ()) : Array (List Nat) × Array Nat × Array Nat :=
  bfs keyL (genTabs.map imgSext) baseSext 3000

@[expose] def sextList (_ : Unit := ()) : Array (List Nat) := (sextData ()).1

@[expose] def nSext : Nat := 1771

@[expose] def sextMap (_ : Unit := ()) : Std.HashMap Nat Nat := indexMap keyL (sextList ())

@[expose] def sextIdx (s : List Nat) : Nat :=
  match (sextMap ())[keyL s]? with
  | some q => if q < nSext && (sextList ())[q]! == s then q else nSext
  | none => nSext

@[expose] def sextOf (t : Nat) : List Nat :=
  sortL (t :: ((octList ()).toList.filter (fun o => o &&& t == t)).map (· ^^^ t))

@[expose] def allLt (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

@[expose] def treeOK {α : Type} [Inhabited α] (l : Array α) (par gen : Array Nat)
    (steps : List (α → α)) (idx : α → Nat) : Bool :=
  par.size == l.size && gen.size == l.size &&
    allLt l.size fun p => p == 0 || (decide (par[p]! < p) && decide (gen[p]! < steps.length) &&
      idx ((steps.getD gen[p]! id) l[par[p]!]!) == p)

@[expose] def octCheck (_ : Unit := ()) : Bool :=
  let L := octList ()
  let D := octData ()
  L.size == nOct && L[0]! == 255 &&
    allLt nOct (fun i =>
      let o := L[i]!
      decide (o < 2 ^ 24) && pop o == 8 && synd o == 0 && octIdx o == i &&
        genTabs.all fun g => decide (octIdx (img g o) < nOct)) &&
    treeOK L D.2.1 D.2.2 (genTabs.map img) octIdx

@[expose] def trioCheck (_ : Unit := ()) : Bool :=
  let L := trioList ()
  let D := trioData ()
  let O := octList ()
  L.size == nTrio && L[0]! == baseTrio &&
    allLt nTrio (fun p =>
      let t := L[p]!
      decide (t.1 < t.2.1) && decide (t.2.1 < t.2.2) &&
        decide (octIdx t.1 < nOct) && decide (octIdx t.2.1 < nOct) &&
        decide (octIdx t.2.2 < nOct) &&
        t.1 &&& t.2.1 == 0 && t.1 &&& t.2.2 == 0 && t.2.1 &&& t.2.2 == 0 &&
        (t.1 ||| t.2.1 ||| t.2.2) == full && trioIdx t == p &&
        genTabs.all fun g => decide (trioIdx (imgTrio g t) < nTrio)) &&
    treeOK L D.2.1 D.2.2 (genTabs.map imgTrio) trioIdx &&
    allLt nOct (fun i => allLt nOct fun j =>
      let a := O[i]!
      let b := O[j]!
      a &&& b != 0 || a == b || decide (trioIdx (sort3 a b (full ^^^ a ^^^ b)) < nTrio))

@[expose] def tetrads0 (_ : Unit := ()) : List Nat :=
  (List.range 24).flatMap fun a => (List.range 24).flatMap fun b => (List.range 24).filterMap
    fun c => if 0 < a && a < b && b < c then some (1 ||| (1 <<< a) ||| (1 <<< b) ||| (1 <<< c))
      else none

@[expose] def sextCheck (_ : Unit := ()) : Bool :=
  let L := sextList ()
  let D := sextData ()
  let O := octList ()
  L.size == nSext && L[0]! == baseSext &&
    allLt nSext (fun q =>
      let s := L[q]!
      s.length == 6 && sortL s == s && s.Pairwise (· < ·) &&
        s.all (fun B => pop B == 4 && decide (B < 2 ^ 24)) &&
        s.foldl (· ||| ·) 0 == full &&
        (s.all fun B => s.all fun B' =>
          B == B' || (B &&& B' == 0 && decide (octIdx (B ||| B') < nOct))) &&
        sextIdx s == q &&
        genTabs.all fun g => decide (sextIdx (imgSext g s) < nSext)) &&
    treeOK L D.2.1 D.2.2 (genTabs.map imgSext) sextIdx &&
    (tetrads0 ()).all fun t =>
      (O.toList.filter (fun o => o &&& t == t)).length == 5 && decide (sextIdx (sextOf t) < nSext)

@[expose] def listChecks (_ : Unit := ()) : Bool := octCheck () && trioCheck () && sextCheck ()

@[expose] def octsT (t : Nat × Nat × Nat) : List Nat := [t.1, t.2.1, t.2.2]

@[expose] def octsS (s : List Nat) : List Nat :=
  s.flatMap fun B => (s.filter (fun B' => B < B')).map (B ||| ·)

@[expose] def trioIn (t : Nat × Nat × Nat) (s : List Nat) : Bool :=
  (octsT t).all fun o => (octsS s).contains o

@[expose] def trioSexts (_ : Unit := ()) : Array (List Nat) :=
  let T := trioList ()
  let S := sextList ()
  (Array.range nTrio).map fun p => (List.range nSext).filter fun q => trioIn T[p]! S[q]!

@[expose] def coplanar (Ts : Array (List Nat)) (p p' : Nat) : Bool :=
  Ts[p]!.any fun q => Ts[p']!.contains q

@[expose] def sextTrios (Ts : Array (List Nat)) (q : Nat) : List Nat :=
  (List.range nTrio).filter fun p => Ts[p]!.contains q

@[expose] def inZeta (l : Nat × Nat × Nat) (o : Nat) : Bool :=
  (octsT l).contains o || (octsT l).any fun u => o &&& u == 0

@[expose] def zc (l k : Nat × Nat × Nat) : Nat := ((octsT k).filter (inZeta l)).length

@[expose] def meets (l k : Nat × Nat × Nat) : Bool := (octsT k).any fun o => (octsT l).contains o

@[expose] def deltaB (Ts : Array (List Nat)) (p₀ p : Nat) : List Bool :=
  let T := trioList ()
  let l := T[p₀]!
  let k := T[p]!
  [p == p₀, p != p₀ && meets l k, !(meets l k) && coplanar Ts p₀ p, zc l k == 1, zc l k == 0]

@[expose] def trioSteps (gs : List (Array Nat)) : List (Nat → Nat) :=
  let T := trioList ()
  gs.map fun g i => trioIdx (imgTrio g T[i]!)

@[expose] def sextSteps (gs : List (Array Nat)) : List (Nat → Nat) :=
  let S := sextList ()
  gs.map fun g i => sextIdx (imgSext g S[i]!)

@[expose] def reachOK (n : Nat) (steps : List (Nat → Nat)) (p : Nat) (c : List Nat) : Bool :=
  let r := bfs (fun i => i) steps p 5000
  let L := r.1
  let par := r.2.1
  let gen := r.2.2
  decide (0 < L.size) && L[0]! == p && par.size == L.size && gen.size == L.size &&
    allLt L.size (fun j => decide (L[j]! < n) && (j == 0 || (decide (par[j]! < j) &&
      decide (gen[j]! < steps.length) && (steps.getD gen[j]! id) L[par[j]!]! == L[j]!))) &&
    c.all fun q => L.contains q

@[expose] def classOrbitCheck (n : Nat) (cls : List (List Nat)) (sizes : List Nat)
    (steps : List (Nat → Nat)) : Bool :=
  cls.length == sizes.length &&
    (List.range n).all (fun p => (cls.filter fun c => c.contains p).length == 1) &&
    (cls.zip sizes).all fun (c, k) => c.length == k &&
      match c with
      | [] => false
      | p :: _ => reachOK n steps p c

@[expose] def deltaCheck (_ : Unit := ()) : Bool :=
  let Ts := trioSexts ()
  let D := (List.range nTrio).map fun p => (p, deltaB Ts 0 p)
  let cls := (List.range 5).map fun i => (D.filter fun e => e.2.getD i false).map (·.1)
  lTabs.all (fun g => imgTrio g baseTrio == baseTrio) &&
    classOrbitCheck nTrio cls [1, 42, 56, 1008, 2688] (trioSteps lTabs) &&
    D.all (fun e =>
      coplanar Ts 0 e.1 == (e.2.getD 0 false || e.2.getD 1 false || e.2.getD 2 false)) &&
    D.all fun e => deltaB Ts e.1 0 == e.2

@[expose] def commonOcts (s s' : List Nat) : Nat :=
  ((octsS s).filter fun o => (octsS s').contains o).length

@[expose] def xiB (q₀ q : Nat) : List Bool :=
  let S := sextList ()
  let c := commonOcts S[q₀]! S[q]!
  [q == q₀, c == 3, c == 1, c == 0]

@[expose] def kappaB (Ts : Array (List Nat)) (q₀ p : Nat) : List Bool :=
  let S := sextList ()
  let T := trioList ()
  let u := octsS S[q₀]!
  let c := ((octsT T[p]!).filter fun o => u.contains o).length
  let inXi1 := Ts[p]!.any fun q => (xiB q₀ q).getD 1 false
  [trioIn T[p]! S[q₀]!, c == 1, c == 0 && inXi1, c == 0 && !inXi1]

@[expose] def sextFactsCheck (_ : Unit := ()) : Bool :=
  let Ts := trioSexts ()
  let X := (List.range nSext).map fun q => (q, xiB 0 q)
  let xcls := (List.range 4).map fun i => (X.filter fun e => e.2.getD i false).map (·.1)
  let K := (List.range nTrio).map fun p => (p, kappaB Ts 0 p)
  let kcls := (List.range 4).map fun i => (K.filter fun e => e.2.getD i false).map (·.1)
  uTabs.all (fun g => imgSext g baseSext == baseSext) &&
    classOrbitCheck nSext xcls [1, 90, 240, 1440] (sextSteps uTabs) &&
    classOrbitCheck nTrio kcls [15, 180, 720, 2880] (trioSteps uTabs)

@[expose] def oneIn (p q : Nat) : Bool :=
  let u := octsS (sextList ())[q]!
  ((octsT (trioList ())[p]!).filter fun o => u.contains o).length == 1

@[expose] def octIn (p q : Nat) : Nat :=
  let u := octsS (sextList ())[q]!
  ((octsT (trioList ())[p]!).filter fun o => u.contains o).headD 0

@[expose] def piCheck (Ts : Array (List Nat)) (l m : Nat) : Bool :=
  let T := trioList ()
  match (Ts[l]!.filter fun q => oneIn m q), (Ts[m]!.filter fun q => oneIn l q) with
  | [π], [π'] =>
    let y := octIn m π
    let x := octIn l π'
    let co := (List.range nTrio).filter fun k => coplanar Ts l k && coplanar Ts m k
    let inPi := fun k => Ts[k]!.contains π
    let inPi' := fun k => Ts[k]!.contains π'
    let pencil := (List.range nTrio).filter fun k => inPi k && (octsT T[k]!).contains y
    let xy := trioIdx (sort3 x y (full ^^^ x ^^^ y))
    co.all (fun k => inPi k || inPi' k) &&
      (co.filter inPi).length == 3 && (co.filter inPi).all (pencil.contains ·) &&
      pencil.length == 3 &&
      pencil.all (fun k => k != m && meets T[m]! T[k]!) &&
      x &&& y == 0 && decide (xy < nTrio) && pencil.contains xy &&
      xy != l && meets T[l]! T[xy]! &&
      pencil.all fun k => k == xy || (!(meets T[l]! T[k]!) && coplanar Ts l k)
  | _, _ => false

@[expose] def stmt310Check (_ : Unit := ()) : Bool :=
  let Ts := trioSexts ()
  let T := trioList ()
  (List.range nTrio).all fun m => zc T[0]! T[m]! != 1 || piCheck Ts 0 m

@[expose] def combs : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: l => (combs k l).map (a :: ·) ++ combs (k + 1) l

@[expose] def discsOvals (Ts : Array (List Nat)) (q : Nat) : List (List Nat) :=
  let T := trioList ()
  let LU := sextTrios Ts q
  let discs := LU.map fun d => LU.filter fun k => k != d && meets T[d]! T[k]!
  let fives := combs 5 LU
  let ovals := fives.filter fun D => D.all fun d => D.all fun k => d == k || !(meets T[d]! T[k]!)
  discs ++ ovals

@[expose] def stmt311Check (_ : Unit := ()) : Bool :=
  let Ts := trioSexts ()
  let T := trioList ()
  let Ds := discsOvals Ts 0
  Ds.length == 21 &&
    (List.range nTrio).all (fun l => Ds.all fun D => D.any fun d =>
      coplanar Ts l d || zc T[l]! T[d]! == 1) &&
    (List.range nSext).all fun q =>
      let tq := sextTrios Ts q
      Ds.all fun D => D.any fun d => tq.any fun k => k == d || coplanar Ts d k

@[expose] def stmt313Check (_ : Unit := ()) : Bool :=
  let Ts := trioSexts ()
  let T := trioList ()
  let LU := sextTrios Ts 0
  let d2 := fun l k => !(meets T[l]! T[k]!) && coplanar Ts l k
  (List.range nTrio).all (fun p => !(oneIn p 0) || LU.all fun m => zc T[m]! T[p]! != 0) &&
    (List.range nTrio).all fun m => zc T[0]! T[m]! != 0 ||
      (List.range nTrio).any fun k => d2 0 k && d2 m k

@[expose] def sextDualCheck (_ : Unit := ()) : Bool :=
  let Ts := trioSexts ()
  let T := trioList ()
  let LU := sextTrios Ts 0
  let mt := fun a b => meets T[a]! T[b]!
  let Sp := (combs 5 LU).filter fun D => D.all fun d => D.all fun k => d == k || !(mt d k)
  let O := octsS (sextList ())[0]!
  LU.length == 15 && Sp.length == 6 &&
    LU.all (fun l => (Sp.filter (·.contains l)).length == 2) &&
    Sp.all (fun D => Sp.all fun D' => D == D' || (D.filter (D'.contains ·)).length == 1) &&
    Sp.all (fun D => O.all fun o => (D.filter fun k => (octsT T[k]!).contains o).length == 1) &&
    (combs 3 LU).all (fun c => !(c.all fun a => c.all fun b => a == b || mt a b) ||
      O.any fun o => c.all fun k => (octsT T[k]!).contains o) &&
    LU.all fun a => LU.all fun b => a == b || (mt a b == !(Sp.any fun D => D.contains a &&
      D.contains b))

end CFSG.Quasithin.H13.AS91.M24G.Native
