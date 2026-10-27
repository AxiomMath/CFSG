module

public import Certificates.Data.FzL26

public section

namespace Certificates.FzR10

open Certificates.FzL26

structure Par where
  e : Nat → Nat → Nat
  tI : Nat
  sI : Nat
  inTL : Nat → Bool
  inW : Nat → Bool
  inTZ : Nat → Bool
  rhoMap : Nat → Nat
  gens : Array Nat

@[expose] def elts : List Nat := List.range 512

@[expose] def invols (P : Par) : List Nat := elts.filter fun x => x != 0 && P.e x x == 0

@[expose] def kord (e : Nat → Nat → Nat) (x : Nat) : Nat :=
  if x = 0 then 1 else if e x x = 0 then 2 else
    if e (e x x) (e x x) = 0 then 4 else
      if e (e (e x x) (e x x)) (e (e x x) (e x x)) = 0 then 8 else 16

@[expose] def conjEdges (P : Par) : List (Nat × Nat) :=
  P.gens.toList.flatMap fun g =>
    let gi := (elts.find? fun h => P.e g h == 0).getD 0
    (invols P).filterMap fun x =>
      let y := P.e (P.e g x) gi
      if P.e y g == P.e g x then some (x, y) else none

@[expose] def tlInvs (P : Par) : List Nat :=
  elts.filter fun l => P.inTL l && l != 0 && P.e l l == 0

@[expose] def ktlEdges (P : Par) : List (Nat × Nat) :=
  (tlInvs P).map fun l => (P.tI, P.e P.tI l)

@[expose] def koutEdges (P : Par) : List (Nat × Nat) :=
  [P.sI, P.e P.tI P.sI].flatMap fun sp =>
    elts.filterMap fun l =>
      if P.inTL l && P.e (P.e l sp) (P.e l sp) == 0 then some (P.e l sp, sp) else none

@[expose] def rhoEdges (P : Par) : List (Nat × Nat) :=
  (invols P).filterMap fun x => if x < 256 then some (x, P.rhoMap x) else none

@[expose] def edges (P : Par) : List (Nat × Nat) :=
  conjEdges P ++ rhoEdges P ++ ktlEdges P ++ koutEdges P

@[expose] def sweep (es : List (Nat × Nat)) (a : Array Nat) : Array Nat :=
  es.foldl (fun (a : Array Nat) (xy : Nat × Nat) =>
    let m := min a[xy.1]! a[xy.2]!
    (a.set! xy.1 m).set! xy.2 m) a

@[expose] def labGo (es : List (Nat × Nat)) : Nat → Array Nat → Array Nat
  | 0, a => a
  | n + 1, a => let a' := sweep es a; if a' == a then a else labGo es n a'

@[expose] def labels (P : Par) : Array Nat := labGo (edges P) 64 (Array.range 512)

@[expose] def bfsStep (e : Nat → Nat → Nat) (gens : Array Nat)
    (st : Array (List Nat) × Array Bool × List Nat) :
    Array (List Nat) × Array Bool × List Nat :=
  st.2.2.foldl (fun (acc : Array (List Nat) × Array Bool × List Nat) x =>
    (List.range gens.size).foldl (fun (acc : Array (List Nat) × Array Bool × List Nat) i =>
      let y := e x gens[i]!
      if y < 512 && !(acc.2.1[y]!) then
        (acc.1.set! y (acc.1[x]! ++ [i]), acc.2.1.set! y true, y :: acc.2.2)
      else acc) acc) (st.1, st.2.1, [])

@[expose] def bfsWords (e : Nat → Nat → Nat) (gens : Array Nat) : Array (List Nat) :=
  ((List.range 32).foldl (fun st _ => bfsStep e gens st)
    (Array.replicate 512 [], (Array.replicate 512 false).set! 0 true, [0])).1

@[expose] def evalW (e : Nat → Nat → Nat) (gens : Array Nat) (w : List Nat) : Nat :=
  w.foldl (fun a i => e a gens[i]!) 0

@[expose] def wordsOK (e : Nat → Nat → Nat) (gens : Array Nat) (wd : Array (List Nat))
    (A : List Nat) : Bool :=
  A.all fun x => evalW e gens wd[x]! == x && wd[x]!.all fun i => i < gens.size

@[expose] def pfW (c : List Bool) (w : List Nat) : Bool :=
  w.foldl (fun a i => xor a c[i]!) false

@[expose] def validF (e : Nat → Nat → Nat) (gens : Array Nat) (wd : Array (List Nat))
    (c : List Bool) (A : List Nat) : Bool :=
  let f := wd.map (pfW c)
  A.all fun x => (List.range gens.size).all fun i =>
    f[e x gens[i]!]! == xor f[x]! c[i]!

@[expose] def vecsOf : Nat → List (List Bool)
  | 0 => [[]]
  | r + 1 => (vecsOf r).flatMap fun v => [false :: v, true :: v]

@[expose] def closedOK (e : Nat → Nat → Nat) (gens : Array Nat) (A : List Nat) : Bool :=
  gens.all (fun g => A.contains g) && A.all fun x => gens.all fun g => A.contains (e x g)

@[expose] def greedyGens (e : Nat → Nat → Nat) (A : List Nat) : Array Nat :=
  (A.foldl (fun (st : Array Nat × Array (List Nat)) x =>
    if x == 0 || st.2[x]! != [] then st
    else
      let gs := st.1.push x
      (gs, bfsWords e gs)) (#[], bfsWords e #[])).1

@[expose] def subs : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => let r := subs l; r ++ r.map (a :: ·)

structure Data where
  wdT : Array (List Nat)
  gensS : Array Nat
  wdS : Array (List Nat)
  m1gens : List Bool → Array Nat
  m1wd : List Bool → Array (List Nat)

@[expose] def slist (P : Par) : List Nat := elts.filter fun x => P.e x P.tI == P.e P.tI x

@[expose] def mkData (P : Par) : Data :=
  let gS := greedyGens P.e (slist P)
  let wdS := bfsWords P.e gS
  { wdT := bfsWords P.e P.gens, gensS := gS, wdS := wdS
    m1gens := fun c => greedyGens P.e ((slist P).filter fun x => !(pfW c wdS[x]!))
    m1wd := fun c => bfsWords P.e (greedyGens P.e ((slist P).filter fun x => !(pfW c wdS[x]!))) }

@[expose] def m1 (P : Par) (D : Data) (c : List Bool) : List Nat :=
  (slist P).filter fun x => !(pfW c D.wdS[x]!)

@[expose] def vecS (P : Par) (D : Data) : List (List Bool) :=
  (vecsOf D.gensS.size).filter fun c =>
    validF P.e D.gensS D.wdS c (slist P) && !(pfW c D.wdS[P.tI]!)

@[expose] def m1OK (P : Par) (D : Data) (c : List Bool) : Bool :=
  let A := m1 P D c
  let g := D.m1gens c
  let w := D.m1wd c
  closedOK P.e g A && wordsOK P.e g w A && A.contains 0

@[expose] def vecH (P : Par) (D : Data) (c : List Bool) : List (List Bool) :=
  let A := m1 P D c
  let g := D.m1gens c
  let w := D.m1wd c
  (vecsOf g.size).filter fun c1 => validF P.e g w c1 A && !(pfW c1 w[P.tI]!)

@[expose] def hmk (P : Par) (D : Data) (c c1 : List Bool) : List Nat :=
  let w := D.m1wd c
  (m1 P D c).filter fun x => !(pfW c1 w[x]!)

@[expose] def hs (P : Par) (D : Data) : List (List Nat) :=
  (vecS P D).flatMap fun c => (vecH P D c).map fun c1 => hmk P D c c1

@[expose] def dataOK (P : Par) (D : Data) : Bool :=
  closedOK P.e P.gens elts && wordsOK P.e P.gens D.wdT elts &&
  closedOK P.e D.gensS (slist P) && wordsOK P.e D.gensS D.wdS (slist P) &&
  (slist P).contains 0 && (slist P).contains P.tI && (vecS P D).all (m1OK P D)

@[expose] def thArr (P : Par) (lab : Array Nat) (Lθ : List Nat) : Array Bool :=
  Array.ofFn (n := 512) fun x =>
    x.val != 0 && P.e x.val x.val == 0 && Lθ.contains lab[x.val]!

@[expose] def keyOf (kd : Array Nat) (th : Array Bool) (x : Nat) : Nat :=
  kd[x]! * 2 + (if th[x]! then 1 else 0)

@[expose] def keyList : List Nat := [2, 3, 4, 5, 8, 9, 16, 17, 32, 33]

@[expose] def sigEq (kd : Array Nat) (th : Array Bool) (A B : List Nat) : Bool :=
  A.length == B.length && keyList.all fun k =>
    A.countP (fun x => keyOf kd th x == k) == B.countP (fun x => keyOf kd th x == k)

@[expose] def kordProf (kd : Array Nat) (A : List Nat) : List Nat :=
  [1, 2, 4, 8, 16].map fun o => A.countP fun x => kd[x]! == o

@[expose] def centOf (P : Par) (u : Nat) : List Nat := elts.filter fun x => P.e x u == P.e u x

@[expose] def profData (P : Par) (kd : Array Nat) (reps : List Nat) (H : List (List Nat)) :
    List (Nat × List Nat × List (List Nat)) :=
  reps.filterMap fun u =>
    let C := centOf P u
    let pc := kordProf kd C
    if 32 ≤ C.length then
      some (u, C, H.filter fun h => h.length == C.length && kordProf kd h == pc)
    else none

@[expose] def coverFail (meet : List (List Nat)) (Lθ : List Nat) : Bool :=
  meet.any fun m => !(m.any fun l => Lθ.contains l)

@[expose] def profFail (kd : Array Nat) (th : Array Bool)
    (pd : List (Nat × List Nat × List (List Nat))) : Bool :=
  pd.any fun q => th[q.1]! && q.2.2.all fun h => !(sigEq kd th h q.2.1)

@[expose] def aliveLabs (P : Par) (lab : Array Nat) : List Nat :=
  ((invols P).map fun x => lab[x]!).eraseDups.filter fun l =>
    l != lab[P.tI]! &&
      !((invols P).any fun x => lab[x]! == l && (P.inTL x || (P.inW x && !P.inTZ x)))

@[expose] def fusionCheckWith (P : Par) (D : Data) : Bool :=
  let lab := labels P
  let lt := lab[P.tI]!
  ((invols P).any fun x => lab[x]! == lt && (P.inTL x || (P.inW x && !P.inTZ x))) ||
  (dataOK P D &&
    let kd := Array.ofFn (n := 512) fun x => kord P.e x.val
    let labT := labGo (conjEdges P) 64 (Array.range 512)
    let reps := (invols P).filter fun x => labT[x]! == x
    let pd := profData P kd reps (hs P D)
    let vt := (vecsOf P.gens.size).filter fun c =>
      validF P.e P.gens D.wdT c elts && pfW c D.wdT[P.tI]!
    let meet := vt.map fun c => (invols P).filterMap fun x =>
      if !(pfW c D.wdT[x]!) then some lab[x]! else none
    (subs (aliveLabs P lab)).all fun sub =>
      let Lθ := lt :: sub
      coverFail meet Lθ || profFail kd (thArr P lab Lθ) pd)

@[expose] def fusionBad (P : Par) : Bool := fusionCheckWith P (mkData P)

@[expose] def parOf (K : PCtx) (t : AutI) (act : Array Nat) : Par where
  e := K.em act
  tI := 64
  sI := 128
  inTL := fun x => t.ap (x % 64) == x % 64 && x / 64 % 4 == 0
  inW := fun x => t.ap (x % 64) == x % 64 && x / 64 < 2
  inTZ := fun x => x / 64 == 1 && x % 64 % 16 == 0
  rhoMap := fun x => rho0 (x % 64) + 64 * (x / 64)
  gens := #[1, 2, 4, 8, 64, 128, 256]

end Certificates.FzR10
