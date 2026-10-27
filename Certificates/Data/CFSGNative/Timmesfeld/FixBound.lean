module

public import Std.Data.HashSet
public import Std.Data.HashMap

public section

namespace Timmesfeld.FixBound

set_option compiler.extract_closed false

@[expose] def actN : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, m => (if m % 2 = 1 then c else 0) ^^^ actN cs (m / 2)

@[expose] def popN : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => a % 2 + popN k (a / 2)

@[expose] def permColsN (a : Array Nat) : List Nat := (List.range 24).map fun j => 2 ^ a[j]!

@[expose] def permN (a : Array Nat) (x : Nat) : Nat := actN (permColsN a) x

@[expose] def syndColsN : List Nat := [62, 129, 65, 193, 61, 514, 258, 770, 59, 2052, 1028, 3076,
  55, 2696, 1352, 4040, 47, 2896, 1744, 3472, 31, 2528, 1952, 3680]

@[expose] def syndN (x : Nat) : Nat := actN syndColsN x

@[expose] def omN : Nat := 16777215

@[expose] def bmN : List Nat := [0x11111e, 0x1111e1, 0x111e11, 0x11e111, 0x1e1111, 0xe11111,
  0xa6c00c, 0x6ca00a, 0x6ac0c0, 0xc6a0a0, 0xcccc00, 0xaaaa00]

@[expose] def amulN (s x : Array Nat) : Array Nat := x.map fun i => s[i]!

@[expose] def bitsBelow (m A : Nat) : List Nat := (List.range m).filter fun j => A.testBit j

@[expose] def maskOf (m : Nat) (p : Nat → Bool) : Nat :=
  (List.range m).foldl (fun acc j => if p j then acc ||| 2 ^ j else acc) 0

@[expose] def codeList (_ : Unit := ()) : Array Nat :=
  bmN.foldl (fun acc b => acc ++ acc.map (· ^^^ b)) #[0]

@[expose] def codeOK (_ : Unit := ()) : Bool :=
  let cl := codeList ()
  cl.size == 4096 && cl.all (fun n => decide (n < 2 ^ 24) && syndN n == 0) &&
    decide cl.toList.Nodup

@[expose] def fixT (a : Array Nat) (n : Nat) : Bool :=
  let y := permN a n ^^^ n
  y == 0 || y == omN

@[expose] def compatT (x y : Nat) : Bool := syndN (x &&& y) == 0

@[expose] def keyN (a : Array Nat) : Nat := a.foldl (fun acc x => acc * 24 + x) 0

@[expose] def mulTab (E : Array (Array Nat)) : Array (Array Nat) :=
  let idx : Std.HashMap Nat Nat :=
    (List.range E.size).foldl (fun m i => m.insert (keyN E[i]!) i) {}
  E.map fun s => E.map fun x => (idx.get? (keyN (amulN s x))).getD E.size

@[expose] def mulOK (E : Array (Array Nat)) : Bool :=
  let T := mulTab E
  (List.range E.size).all fun i => (List.range E.size).all fun j =>
    decide (T[i]![j]! < E.size) && E[T[i]![j]!]! == amulN E[i]! E[j]!

@[expose] def extendS (T : Array (Array Nat)) (S : List Nat) (x : Nat) : List Nat :=
  (S ++ S.map fun s => T[x]![s]!).mergeSort (fun a b => decide (a ≤ b))

@[expose] def okExt (T : Array (Array Nat)) (S : List Nat) (x : Nat) : Bool :=
  !S.contains x && T[x]![x]! == 0 && S.all fun s => T[x]![s]! == T[s]![x]!

@[expose] def nextLevel (E : Array (Array Nat)) (T : Array (Array Nat))
    (H : Std.HashSet (List Nat)) (L : Array (List Nat)) :
    Std.HashSet (List Nat) × Array (List Nat) := Id.run do
  let mut seen := H
  let mut out : Array (List Nat) := #[]
  for S in L do
    for x in [0:E.size] do
      if okExt T S x then
        let U := extendS T S x
        if !seen.contains U then
          seen := seen.insert U
          out := out.push U
  return (seen, out)

@[expose] def levels (E : Array (Array Nat)) (T : Array (Array Nat)) : Nat →
    Std.HashSet (List Nat) → Array (List Nat) → Array (List Nat) → Array (List Nat)
  | 0, _, _, acc => acc
  | fuel + 1, H, cur, acc =>
      let (H', nxt) := nextLevel E T H cur
      if nxt.size == 0 then acc else levels E T fuel H' nxt (acc ++ nxt)

@[expose] def subsList (E : Array (Array Nat)) : Array (List Nat) :=
  let T := mulTab E
  levels E T 16 (Std.HashSet.ofList [[0]]) #[ [0] ] #[ [0] ]

@[expose] def subsOK (E : Array (Array Nat)) : Bool :=
  let T := mulTab E
  let L := subsList E
  let H : Std.HashSet (List Nat) := Std.HashSet.ofList L.toList
  L.contains [0] && L.all (fun S => S.contains 0 && S.all (fun s => decide (s < E.size)) &&
    (List.range E.size).all fun x => !okExt T S x || H.contains (extendS T S x))

@[expose] def fixList (E : Array (Array Nat)) (cl : Array Nat) (S : List Nat) : Array Nat :=
  cl.filter fun n => S.all fun i => fixT E[i]! n

@[expose] def basicMask (F : Array Nat) (z : Nat) : Nat :=
  maskOf F.size fun j => compatT F[j]! z

@[expose] def famClose (basics : Array Nat) (full : Nat) : Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert full
  let mut fam : Array Nat := #[full]
  let mut frontier : Array Nat := #[full]
  for _ in [0:64] do
    let mut next : Array Nat := #[]
    for A in frontier do
      for b in basics do
        let I := A &&& b
        if !seen.contains I then
          seen := seen.insert I
          fam := fam.push I
          next := next.push I
    frontier := next
  return fam

@[expose] def mGens (E : Array (Array Nat)) (S : List Nat) : List Nat :=
  omN :: S.flatMap fun i => bmN.map fun b => permN E[i]! b ^^^ b

@[expose] def lowIdx (r : Nat) : Nat :=
  let rec go (k : Nat) (x : Nat) : Nat :=
    match k with
    | 0 => 0
    | k + 1 => if x % 2 = 1 then 24 - (k + 1) else go k (x / 2)
  go 24 r

@[expose] def rankCert (gens : List Nat) : List Nat × List Nat := Id.run do
  let ga := gens.toArray
  let mut rows : Array (Nat × Nat × Nat) := #[]
  let mut ws : Array Nat := #[]
  let mut ps : Array Nat := #[]
  for pos in [0:ga.size] do
    let v := ga[pos]!
    let mut r := v
    let mut t := 2 ^ pos
    for q in [0:rows.size] do
      let (rr, pp, tt) := rows[q]!
      if r.testBit pp then
        r := r ^^^ rr
        t := t ^^^ tt
    if r != 0 then
      let p := lowIdx r
      rows := rows.map (fun row =>
        let (rr, pp, tt) := row
        if rr.testBit p then (rr ^^^ r, pp, tt ^^^ t) else row)
      rows := rows.push (r, p, t)
      ws := ws.push v
      ps := ps.push pos
  let mut fs : Array Nat := #[]
  for i in [0:ps.size] do
    let pi := ps[i]!
    let mut f := 0
    for k in [0:rows.size] do
      let (_, pk, tk) := rows[k]!
      if tk.testBit pi then f := f ||| 2 ^ pk
    fs := fs.push f
  return (ws.toList, fs.toList)

@[expose] def dualOK (ws fs : List Nat) : Bool :=
  ws.length == fs.length && (List.range ws.length).all fun i => (List.range ws.length).all fun j =>
    popN 24 (fs[i]! &&& ws[j]!) % 2 == if i == j then 1 else 0

@[expose] def memberOK (S : List Nat) (F basics : Array Nat) (Mws : List Nat) (A : Nat) : Bool :=
  let m := F.size
  let Z := (List.range m).foldl (fun acc j => if A.testBit j then acc &&& basics[j]! else acc)
    (2 ^ m - 1)
  let Al := (bitsBelow m A).map fun j => F[j]!
  let Zl := (bitsBelow m Z).map fun j => F[j]!
  let c := rankCert (Mws ++ Al ++ Zl)
  dualOK c.1 c.2 && c.1.all (fun w => Mws.contains w || Al.contains w || Zl.contains w) &&
    decide (Al.length * S.length * 2 ^ 11 * Zl.length ≤ 2 ^ 14 * 2 ^ c.1.length)

@[expose] def sOK (E : Array (Array Nat)) (cl : Array Nat) (S : List Nat) : Bool :=
  let F := fixList E cl S
  let m := F.size
  let full := 2 ^ m - 1
  let basics := F.map (basicMask F)
  let fam := famClose basics full
  let H : Std.HashSet Nat := Std.HashSet.ofList fam.toList
  let Mg := mGens E S
  let Mws := (rankCert Mg).1
  H.contains full && fam.all (fun A => basics.all fun b => H.contains (A &&& b)) &&
    Mws.all (fun w => Mg.contains w) && fam.all (memberOK S F basics Mws)

@[expose] def famOK (E : Array (Array Nat)) : Bool :=
  let cl := codeList ()
  (subsList E).all fun S => S.length == 1 || sOK E cl S

@[expose] def omegaOK (E : Array (Array Nat)) : Bool :=
  let cl := codeList ()
  (subsList E).all fun S =>
    S.length == 1 ||
      (let F := fixList E cl S
       let Mg := mGens E S
       let Mws := (rankCert Mg).1
       let c := rankCert (Mws ++ F.toList)
       Mws.all (fun w => Mg.contains w) && dualOK c.1 c.2 &&
         c.1.all (fun w => Mws.contains w || F.contains w) &&
         decide (2 * S.length * 2 ^ (11 : Nat) * F.size ≤ 2 ^ (14 : Nat) * 2 ^ c.1.length))

@[expose] def span8 (a b c : Nat) : List Nat :=
  [0, a, b, a ^^^ b, c, a ^^^ c, b ^^^ c, a ^^^ b ^^^ c]

@[expose] def trivOK (_ : Unit := ()) : Bool :=
  let cl := codeList ()
  cl.all fun x1 => x1 == 0 || x1 == omN || (
    let K1 := cl.filter (compatT x1)
    K1.all fun x2 => [0, omN, x1, x1 ^^^ omN].contains x2 ||
      K1.all fun x3 => !compatT x2 x3 || (span8 omN x1 x2).contains x3)

end Timmesfeld.FixBound
