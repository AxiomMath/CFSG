module

public import Certificates.Data.CFSGNative.LargeExtraspecialFin4.Basic

public section

namespace CFSG.LargeExtraspecial.Fin4.Native

set_option compiler.extract_closed false

@[expose] def wordVal (w : List Nat) : Nat := w.foldr mulC idC

@[expose] def wordOK (gs w : List Nat) (t : Nat) : Bool := w.all (gs.contains ·) && wordVal w == t

@[expose] def bfsLayer (gs : List Nat) (seen : Std.HashSet Nat) (front : List (Nat × List Nat)) :
    Std.HashSet Nat × List (Nat × List Nat) :=
  front.foldl (fun acc xw => gs.foldl (fun acc s =>
    let y := mulC s xw.1
    if acc.1.contains y then acc else (acc.1.insert y, (y, s :: xw.2) :: acc.2)) acc) (seen, [])

@[expose] def bfsLoop (gs : List Nat) : Nat → Std.HashSet Nat → List (Nat × List Nat) →
    List (Nat × List Nat) → List (Nat × List Nat)
  | 0, _, _, acc => acc
  | n + 1, seen, front, acc =>
    if front.isEmpty then acc else
      let r := bfsLayer gs seen front
      bfsLoop gs n r.1 r.2 (r.2 ++ acc)

@[expose] def bfsWords (gs : List Nat) : List (Nat × List Nat) :=
  bfsLoop gs 1000 ((∅ : Std.HashSet Nat).insert idC) [(idC, [])] [(idC, [])]

@[expose] def wordMap (L : List (Nat × List Nat)) : Std.HashMap Nat (List Nat) :=
  L.foldl (fun m xw => m.insert xw.1 xw.2) ∅

@[expose] def memW (M : Std.HashMap Nat (List Nat)) (gs : List Nat) (t : Nat) : Bool :=
  match M[t]? with
  | some w => wordOK gs w t
  | none => false

@[expose] def gensOf (node : List (Nat × List Nat)) : List Nat := node.flatMap (·.2)

@[expose] def conjBad (h : Nat) (node : List (Nat × List Nat)) : Bool :=
  node.any fun p => node.any fun q =>
    app h p.1 == q.1 && !setEq (p.2.map (mulC h ·)) (q.2.map (mulC · h))

@[expose] def inconsistent (gs : List Nat) (H : List (Nat × List Nat))
    (node : List (Nat × List Nat)) : Bool :=
  H.any fun hw => wordOK gs hw.2 hw.1 && conjBad hw.1 node

@[expose] def transOK (gs : List Nat) (H : List (Nat × List Nat)) : Bool :=
  (List.range 16).all fun w => w == 0 || H.any fun hw => app hw.1 1 == w && wordOK gs hw.2 hw.1

@[expose] def findT (H : List (Nat × List Nat)) (w : Nat) : Nat × List Nat :=
  (H.find? fun hw => app hw.1 1 == w).getD (0, [])

@[expose] def findInv (H : List (Nat × List Nat)) (h : Nat) : Nat × List Nat :=
  (H.find? fun hw => mulC hw.1 h == idC).getD (0, [])

@[expose] def famL (H : List (Nat × List Nat)) (LE : List Nat) (w : Nat) : List Nat :=
  let t := (findT H w).1
  let t' := (findInv H t).1
  LE.map fun e => mulC (mulC t e) t'

@[expose] def famOK (gs : List Nat) (H : List (Nat × List Nat)) : Bool :=
  (List.range 16).all fun w => w == 0 ||
    let t := findT H w
    let t' := findInv H t.1
    app t.1 1 == w && mulC t'.1 t.1 == idC && wordOK gs t.2 t.1 && wordOK gs t'.2 t'.1

@[expose] def derGens (_ : Unit) : List Nat :=
  ((List.range 16).filter (· != 0)).flatMap fun x =>
    ((List.range 16).filter (· != 0)).map fun y => mulC (tauC x) (tauC y)

@[expose] def a6OK (gs : List Nat) : Bool :=
  let D := derGens ()
  let MD := wordMap (bfsWords D)
  let M := wordMap (bfsWords gs)
  gs.all (memW MD D ·) && D.all (memW M gs ·)

@[expose] def closedOK (gK LK : List Nat) : Bool :=
  LK.contains idC && LK.all fun x => gK.all fun s => LK.contains (mulC s x)

@[expose] def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

@[expose] def pointOK (gs gK : List Nat) (MK : Std.HashMap Nat (List Nat)) (Lw : List Nat) :
    Bool :=
  Lw.all (memW MK gK ·) ||
    let g2 := gK ++ Lw
    let M2 := wordMap (bfsWords g2)
    gs.all (memW M2 g2 ·)

@[expose] def smallOK (gs gK : List Nat) (F : Nat → List Nat) (LK : List Nat)
    (MK : Std.HashMap Nat (List Nat)) : Bool :=
  closedOK gK LK && LK.all (memW MK gK ·) && nodupB LK && LK.length == 60 &&
    (List.range 16).all fun w => w == 0 || pointOK gs gK MK (F w)

@[expose] def pairOK (gs : List Nat) (F : Nat → List Nat) (isA6 : Bool) (b c : Nat) : Bool :=
  let gK := F b ++ F c
  let HK := bfsWords gK
  let MK := wordMap HK
  gs.all (memW MK gK ·) || (isA6 && smallOK gs gK F (HK.map (·.1)) MK)

@[expose] def leafOK (gs : List Nat) (H : List (Nat × List Nat)) (LE : List Nat) : Bool :=
  let A := a6OK gs
  famOK gs H && (List.range 16).all fun b => (List.range 16).all fun c =>
    b == 0 || c == 0 || !Jn b c || pairOK gs (famL H LE) A b c

@[expose] def pickNext (H : List (Nat × List Nat)) (node : List (Nat × List Nat)) : Nat :=
  let free := (List.range 16).filter fun d =>
    d != 0 && !(H.any fun hw => node.any fun p => app hw.1 p.1 == d)
  (free.filter (Jn 1 ·) ++ free).headD 0

@[expose] def nodeWith (LE : List Nat) (rest : List (Nat × List Nat)) (recur : Nat → Bool) :
    Bool :=
  let node := (1, LE) :: rest
  let gs := gensOf node
  let H := bfsWords gs
  inconsistent gs H node || if transOK gs H then leafOK gs H LE else recur (pickNext H node)

@[expose] def nodeOK : Nat → List Nat → List (Nat × List Nat) → Bool
  | 0, LE, rest => nodeWith LE rest fun _ => false
  | f + 1, LE, rest => nodeWith LE rest fun d =>
    d != 0 && d < 16 && (cand d).all fun L => nodeOK f LE (rest ++ [(d, L)])

@[expose] def topOK (_ : Unit) : Bool := (cand 1).all fun L => nodeOK 2 L []

end CFSG.LargeExtraspecial.Fin4.Native
