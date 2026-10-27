module

public import Certificates.Data.S1277Cand
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic

public section

namespace Certificates.Data.S1277Surv

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct Certificates.Data.S1277Cand
  Certificates.Data.S1277Sig Certificates.Data.S1277Bfs Std

@[expose] def packC (cols : List Nat) : Nat := cols.foldr (fun c acc => c + 64 * acc) 0

@[expose] def unpackC (d x : Nat) : List Nat := (List.range d).map fun i => (x / 64 ^ i) % 64

@[expose] def app6 (x v : Nat) : Nat :=
  (if v % 2 = 1 then x % 64 else 0) ^^^ ((if (v / 2) % 2 = 1 then (x / 64) % 64 else 0) ^^^
  ((if (v / 4) % 2 = 1 then (x / 4096) % 64 else 0) ^^^
  ((if (v / 8) % 2 = 1 then (x / 262144) % 64 else 0) ^^^
  ((if (v / 16) % 2 = 1 then (x / 16777216) % 64 else 0) ^^^
  (if (v / 32) % 2 = 1 then (x / 1073741824) % 64 else 0)))))

@[expose] def mulSSpec (x y : Nat) : Nat := packC (compCols (unpackC 6 x) (unpackC 6 y))

@[expose] def mulS (x y : Nat) : Nat :=
  app6 x (y % 64) + 64 * (app6 x ((y / 64) % 64) + 64 * (app6 x ((y / 4096) % 64) +
    64 * (app6 x ((y / 262144) % 64) + 64 * (app6 x ((y / 16777216) % 64) +
      64 * app6 x ((y / 1073741824) % 64)))))

@[expose] def oneS : Nat := 1 + 64 * (2 + 64 * (4 + 64 * (8 + 64 * (16 + 64 * 32))))

@[expose] def closW (gens : List Nat) (fuel : Nat) : HashSet Nat :=
  bfs (gens.map fun g y => mulS y g) (oneS :: gens) fuel

@[expose] def closedW (gens : List Nat) (C : HashSet Nat) : Bool :=
  C.toList.all fun y => gens.all fun g => C.contains (mulS y g)

@[expose] def nodeValidW (cap : Nat) (N : Node) : Bool :=
  let C := closW N.gens (cap + 1)
  decide (C.size ≤ cap) && closedW N.gens C && N.elems == sortSet C && subsetL N.gens N.elems

@[expose] def cosetTab (S : Node) (sigP : List Nat) : HashMap Nat Nat × List Nat :=
  (oneS :: sigP).foldl (fun (st : HashMap Nat Nat × List Nat) x =>
    if st.1.contains x then st
    else (S.elems.foldl (fun t s => t.insert (mulS s x) x) st.1, x :: st.2)) (∅, [])

@[expose] def cosetUnion (S : Node) (O : HashSet Nat) : HashSet Nat :=
  O.toList.foldl (fun a c => S.elems.foldl (fun a' s => a'.insert (mulS s c)) a) ∅

@[expose] def cosetOrbit (cap : Nat) (S : Node) (tab : HashMap Nat Nat) (g : Nat) : HashSet Nat :=
  bfs ((S.gens ++ [g]).map fun h c => tab.getD (mulS c h) 0) [oneS] (cap / S.elems.length + 1)

@[expose] def capOK (cap : Nat) (nodes : List Node) (S : Node) (tab : HashMap Nat Nat) (g : Nat) :
    Bool :=
  let O := cosetOrbit cap S tab g
  decide (cap / S.elems.length < O.size) ||
    nodes.any fun N => N.elems == sortSet (cosetUnion S O)

@[expose] def latOK (cap : Nat) (sigP : List Nat) (nodes : List Node) (S0 : Node) : Bool :=
  nodes.any (fun N => N == S0) &&
  nodes.all fun S =>
    let ct := cosetTab S sigP
    nodeValidW cap S && sigP.all ct.1.contains &&
    ct.2.all (fun c => S.elems.all fun s => ct.1.getD (mulS s c) 0 == c) &&
    ct.2.all (capOK cap nodes S ct.1)

@[expose] def shortGens (cap : Nat) (gens : List Nat) : List Nat :=
  gens.foldl (fun (acc : List Nat) g => if (closW acc (cap + 1)).contains g then acc else acc ++ [g]) []

@[expose] def survRound (cap : Nat) (sigP : List Nat) (known : HashSet (List Nat))
    (frontier : List Node) : List Node :=
  distinctNodes (frontier.flatMap fun S =>
    let ct := cosetTab S sigP
    ct.2.filterMap fun g =>
      let O := cosetOrbit cap S ct.1 g
      if decide (cap / S.elems.length < O.size) then none
      else
        let C := sortSet (cosetUnion S O)
        if known.contains C then none else some (⟨S.gens ++ [g], C⟩ : Node))

@[expose] def survLoop (cap : Nat) (sigP : List Nat) : Nat → List Node → List Node → List Node
  | 0, nodes, _ => nodes
  | n + 1, nodes, frontier =>
    if frontier.isEmpty then nodes
    else
      let known : HashSet (List Nat) := nodes.foldl (fun s N => s.insert N.elems) ∅
      let new := survRound cap sigP known frontier
      survLoop cap sigP n (nodes ++ new) new

@[expose] def survNodes (cap : Nat) (sigP : List Nat) (S0 : Node) (fuel : Nat) : List Node :=
  survLoop cap sigP fuel [S0] [S0]

@[expose] def span3 (a b c : Nat) : List Nat :=
  (List.range 8).map fun e =>
    (if e.testBit 0 then a else 0) ^^^ (if e.testBit 1 then b else 0) ^^^
      (if e.testBit 2 then c else 0)

@[expose] def invSubs (gens : List Nat) : List (List Nat) :=
  let subs := (List.range 64).flatMap fun a => (List.range 64).flatMap fun b =>
    (List.range 64).filterMap fun c =>
      if a != 0 && a < b && b < c then
        let sp := span3 a b c
        if decide sp.Nodup && gens.all (fun g => sp.all fun x => sp.contains (applyCols (unpackC 6 g) x))
        then some (sp.mergeSort) else none
      else none
  (subs.foldl (fun (st : List (List Nat) × HashSet (List Nat)) sp =>
    if st.2.contains sp then st else (sp :: st.1, st.2.insert sp)) ([], ∅)).1.reverse

@[expose] def findPair (gens : List Nat) : Option (List Nat × List Nat) :=
  let subs := invSubs gens
  (subs.flatMap fun N1 => subs.filterMap fun N2 =>
    if N1.all (fun a => a == 0 || !N2.contains a) then some (N1, N2) else none).head?

@[expose] def xorCombo (u : List Nat) (e : Nat) : Nat :=
  (if e.testBit 0 then u.getD 0 0 else 0) ^^^ (if e.testBit 1 then u.getD 1 0 else 0) ^^^
    (if e.testBit 2 then u.getD 2 0 else 0)

@[expose] def basis3 (N1 : List Nat) : List Nat :=
  let u0 := (N1.filter (· != 0)).headD 0
  let u1 := (N1.filter (fun x => x != 0 && x != u0)).headD 0
  let u2 := (N1.filter (fun x => !((span3 u0 u1 0).contains x))).headD 0
  [u0, u1, u2]

@[expose] def coordOf (u : List Nat) (x : Nat) : Nat :=
  (List.range 8).findIdx fun e => xorCombo u e == x

@[expose] def restr (u : List Nat) (s : Nat) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j =>
    if (coordOf u (applyCols (unpackC 6 s) (u.getD j.1 0))).testBit i.1 then 1 else 0


@[expose] def survGensK (T : KTab) (N Pl : List Nat) (d : Nat) (tab : HashMap Nat Nat) : List Nat :=
  let basis := basisOf T N Pl
  (kgensOf T).map fun g => packC ((List.range d).map fun i =>
    tab.getD (mulN T (mulN T g (repOf T basis (2 ^ i))) (invN T g)) 0)

@[expose] def repOK (T : KTab) (N Pl : List Nat) (d : Nat) (tab : HashMap Nat Nat) : Bool :=
  let basis := basisOf T N Pl
  (List.range d).all fun i =>
    N.contains (repOf T basis (2 ^ i)) && tab.getD (repOf T basis (2 ^ i)) 0 == 2 ^ i

@[expose] def kgensOK (T : KTab) : Bool := (kgensOf T).all fun g => decide (g < T.nb * 64)

@[expose] def vlCheck (T : KTab) (N : List Nat) (tab : HashMap Nat Nat) (S : Node)
    (N1 N2 : List Nat) : Bool :=
  let u := basis3 N1
  let NA := N.filter fun x => N1.contains (tab.getD x 0)
  let NB := N.filter fun x => N2.contains (tab.getD x 0)
  decide (S.elems.length = 168) && N1.contains 0 && N2.contains 0 &&
  N1.all (fun a => decide (a < 64)) && N2.all (fun a => decide (a < 64)) &&
  N1.all (fun a => N1.all fun b => N1.contains (a ^^^ b)) &&
  N2.all (fun a => N2.all fun b => N2.contains (a ^^^ b)) &&
  N1.all (fun a => a == 0 || !N2.contains a) &&
  (List.range 64).all (fun c => N1.any fun a => N2.any fun b => a ^^^ b == c) &&
  S.elems.all (fun s => N1.all (fun a => N1.contains (applyCols (unpackC 6 s) a)) &&
    N2.all (fun a => N2.contains (applyCols (unpackC 6 s) a))) &&
  decide (NA.length = 16) && decide (NB.length = 16) &&
  NA.all (fun x => NA.all fun y => mulN T x y == mulN T y x) &&
  NA.all (fun x => mulN T x x == oneN T) &&
  NB.all (fun x => NB.all fun y => mulN T x y == mulN T y x) &&
  NB.all (fun x => mulN T x x == oneN T) &&
  S.elems.all (fun a => S.elems.all fun b =>
    decide (restr u (mulS a b) = restr u a * restr u b)) &&
  S.elems.all (fun a => decide ((restr u a).det = 1)) &&
  S.elems.all (fun a => decide (restr u a = 1 → a = oneS))

@[expose] def vlOK (T : KTab) (N : List Nat) (tab : HashMap Nat Nat) (S : Node) : Bool :=
  match findPair S.gens with
  | some (N1, N2) => vlCheck T N tab S N1 N2
  | none => false

@[expose] def eCheck (T : KTab) (N Pl : List Nat) (zN : Nat) : Bool :=
  N.all (fun x => !(N.all fun y => mulN T x y == mulN T y x) || Pl.contains x) &&
  N.any fun x => N.any fun y => commN T x y == zN

@[expose] def survCheck (T : KTab) (N : List Nat) (zN : Nat) (Pl : List Nat) (d typ : Nat)
    (tab : HashMap Nat Nat) (sl : List (List Nat)) : Bool :=
  let n := N.length
  let kk := (klist T).length
  let e := kk / n
  let s := sl.length
  let cap := e * 105
  let sigP := sl.map packC
  let gensK := survGensK T N Pl d tab
  let sg := shortGens cap gensK
  let S0 : Node := ⟨sg, sortSet (closW sg (cap + 1))⟩
  let nodes := survNodes cap sigP S0 3
  decide (d = 6) && decide (typ = 1) && plOK T Pl && frOK T N Pl d tab &&
  phiOK T zN Pl N typ d tab &&
  decide (Pl.length = 2) && Pl.contains zN && (zN != oneN T) && (mulN T zN zN == oneN T) &&
  n * e == kk && s % e == 0 && (List.range 20).any (fun j => s / e == 105 * 2 ^ j) &&
  kgensOK T && repOK T N Pl d tab && decide (S0.elems.length = e) && latOK cap sigP nodes S0 &&
  eCheck T N Pl zN &&
  nodes.all fun S => S.elems == S0.elems || (S.elems.length / e) % 2 == 0 || vlOK T N tab S

@[expose] def survOK (T : KTab) (N : List Nat) (zN : Nat) : Bool :=
  let Pl := phiList T N
  let d := Nat.log2 (N.length / Pl.length)
  let typ := if Pl.length == 1 then 0 else if Pl.length == 2 then 1 else 2
  let tab := codeTab T N Pl d
  let pt := phiTab T zN Pl N typ d tab
  survCheck T N zN Pl d typ tab (sigList d (phiFn pt))

end Certificates.Data.S1277Surv

end
