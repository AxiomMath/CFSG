module

public import Std.Data.HashSet

public section

set_option compiler.extract_closed false

namespace CFSG.GammaU.Native

@[expose] def q0b (n : Nat) : Bool :=
  (List.range 6).foldl (fun acc i => acc ^^ (n.testBit i || n.testBit (i + 6))) false

@[expose] def theta0N (n : Nat) : Nat := (n >>> 6) ||| (((n &&& 63) ^^^ (n >>> 6)) <<< 6)

@[expose] def appN (rows : Array Nat) (n : Nat) : Nat :=
  let a0 := if n.testBit 0 then 0 ^^^ rows[0]! else 0
  let a1 := if n.testBit 1 then a0 ^^^ rows[1]! else a0
  let a2 := if n.testBit 2 then a1 ^^^ rows[2]! else a1
  let a3 := if n.testBit 3 then a2 ^^^ rows[3]! else a2
  let a4 := if n.testBit 4 then a3 ^^^ rows[4]! else a3
  let a5 := if n.testBit 5 then a4 ^^^ rows[5]! else a4
  let a6 := if n.testBit 6 then a5 ^^^ rows[6]! else a5
  let a7 := if n.testBit 7 then a6 ^^^ rows[7]! else a6
  let a8 := if n.testBit 8 then a7 ^^^ rows[8]! else a7
  let a9 := if n.testBit 9 then a8 ^^^ rows[9]! else a8
  let a10 := if n.testBit 10 then a9 ^^^ rows[10]! else a9
  if n.testBit 11 then a10 ^^^ rows[11]! else a10

@[expose] def f0b (m n : Nat) : Bool :=
  (List.range 6).foldl
    (fun acc i => acc ^^ ((m.testBit i && n.testBit (6 + i)) ^^ (m.testBit (6 + i) && n.testBit i)))
    false

@[expose] def spanList : List Nat → List Nat
  | [] => [0]
  | v :: vs => spanList vs ++ (spanList vs).map (· ^^^ v)

@[expose] def lagrCand (a0 : Nat) : List Nat :=
  (List.range 4096).filter fun n => n != 0 && n != a0 && !q0b n && !f0b n a0

@[expose] def lagrDFS : Nat → List Nat → List Nat → List (List Nat)
  | 0, vs, _ => [vs]
  | k + 1, vs, cands =>
    let S := spanList vs
    cands.flatMap fun v =>
      if v ∉ S ∧ ∀ s ∈ S, v ≤ v ^^^ s then
        lagrDFS k (v :: vs) (cands.filter fun w => decide (v < w) && !f0b w v)
      else []

@[expose] def bfsRound {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ))
    (frontier : List σ) (seen : Std.HashSet κ) : List σ × Std.HashSet κ :=
  (frontier.flatMap fun s => fs.map fun f => f s).foldl
    (fun (acc : List σ × Std.HashSet κ) t =>
      match acc with
      | (l, h) => if h.contains (key t) then (l, h) else (t :: l, h.insert (key t)))
    ([], seen)

@[expose] def bfsClosure {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ)) :
    Nat → List σ → Std.HashSet κ → List σ → List σ
  | 0, frontier, _, visited => frontier ++ visited
  | fuel + 1, frontier, seen, visited =>
    let r := bfsRound key fs frontier seen
    if r.1.isEmpty then frontier ++ visited
    else bfsClosure key fs fuel r.1 r.2 (frontier ++ visited)

@[expose] def extDFS {α : Type} (cand : List α → List α) : Nat → List α → List (List α)
  | 0, pre => [pre]
  | k + 1, pre => (cand pre).flatMap fun c => extDFS cand k (pre ++ [c])

@[expose] def a0 : Nat := 3072

@[expose] def gamuGens : List (Array Nat) :=
  [#[1, 2, 32, 8, 16, 4, 64, 128, 2048, 512, 1024, 256],
    #[2, 4, 1112, 1097, 32, 25, 128, 256, 593, 1553, 2048, 1600],
    #[64, 2, 4, 8, 16, 32, 65, 128, 256, 512, 1024, 2048],
    #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]]

@[expose] def saGens : List (Array Nat) :=
  [#[952, 269, 3463, 3833, 2201, 1193, 3638, 841, 497, 3650, 1659, 2683],
    #[3778, 3961, 444, 3270, 413, 429, 3707, 317, 3718, 3443, 1734, 2758]]

@[expose] def dReps : List (List Nat) :=
  [[960, 48, 9, 5, 3, 3072],
    [961, 48, 9, 5, 3, 3072],
    [1072, 960, 9, 5, 3, 3072],
    [1072, 961, 9, 5, 3, 3072],
    [768, 192, 48, 12, 3, 3072],
    [1072, 768, 192, 12, 3, 3072]]

@[expose] def d0 : List Nat := [961, 48, 9, 5, 3, 3072]

@[expose] def ws : List Nat := [3072, 1, 2, 4, 8, 16]

@[expose] def coefW : List Nat := [4, 16, 64, 256, 1024, 1027, 8, 32, 128, 512, 2048, 2049]

@[expose] def k0 : Array Nat := #[1, 2, 4, 8, 32, 16, 64, 128, 256, 512, 2048, 1024]

@[expose] def cBasis : List (Array Nat) :=
  [#[1, 2, 3076, 3080, 796, 812, 64, 128, 3376, 3632, 1036, 2060],
    #[1, 3074, 4, 3080, 666, 682, 64, 3248, 256, 3632, 1034, 2058],
    #[3073, 2, 4, 3080, 601, 617, 3184, 128, 256, 3632, 1033, 2057],
    #[49, 50, 52, 3128, 535, 551, 3136, 3200, 3328, 560, 1992, 3016],
    #[14, 13, 11, 7, 1040, 2080, 910, 845, 715, 455, 1024, 2048]]

@[expose] def idR : Array Nat := #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

@[expose] def mulR (g h : Array Nat) : Array Nat := h.map (appN g)

@[expose] def isoN (r : Array Nat) : Bool :=
  r.size == 12 && r.all (· < 4096) && (List.range 4096).all fun n => q0b (appN r n) == q0b n

@[expose] def unitaryN (r : Array Nat) : Bool :=
  (List.range 12).all fun j => appN r (theta0N (2 ^ j)) == theta0N (appN r (2 ^ j))

@[expose] def antiN (r : Array Nat) : Bool :=
  (List.range 12).all fun j => appN r (theta0N (2 ^ j)) == theta0N (theta0N (appN r (2 ^ j)))

@[expose] def gammaUN (r : Array Nat) : Bool := isoN r && (unitaryN r || antiN r)

@[expose] def keyD (s : List Nat) : List Nat := (spanList s).mergeSort (· ≤ ·)

@[expose] def thetaPow (e y : Nat) : Nat := if e = 1 then theta0N y else theta0N (theta0N y)

@[expose] def subsetProducts (gens : List (Array Nat)) : List (Array Nat) :=
  gens.foldl (fun acc g => acc ++ acc.map (mulR g)) [idR]

@[expose] def compOf (c : Nat) : List (Array Nat) :=
  subsetProducts ((List.range 5).map fun i =>
    if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!)

@[expose] def conjC (g gi : Array Nat) (C : List (Array Nat)) : List (Array Nat) :=
  C.map fun x => mulR (mulR g x) gi

@[expose] def gamuInv : List (Array Nat) :=
  [#[1, 2, 32, 8, 16, 4, 64, 128, 2048, 512, 1024, 256],
    #[804, 1, 2, 44, 808, 16, 2572, 64, 128, 2816, 2316, 1024],
    #[65, 2, 4, 8, 16, 32, 1, 128, 256, 512, 1024, 2048],
    #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]]

@[expose] def saInv : List (Array Nat) :=
  [#[574, 3908, 454, 635, 2841, 1833, 4022, 313, 385, 3826, 1653, 2677],
    #[761, 3956, 3466, 245, 733, 749, 3211, 637, 3894, 3459, 1419, 2443]]

@[expose] def theta0R : Array Nat := #[64, 128, 256, 512, 1024, 2048, 65, 130, 260, 520, 1040, 2080]

@[expose] def closureTr {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ)
    (act : Array Nat → σ → σ) (gens : List (Array Nat × Array Nat)) (fuel : Nat) (start : σ) :
    List (σ × Array Nat × Array Nat) :=
  bfsClosure (fun p => key p.1)
    (gens.map fun gg p => (act gg.1 p.1, mulR gg.1 p.2.1, mulR p.2.2 gg.2)) fuel
    [(start, idR, idR)] ((∅ : Std.HashSet κ).insert (key start)) []

@[expose] def singT (_ : Unit := ()) : List (Nat × Array Nat × Array Nat) :=
  closureTr id appN (gamuGens.zip gamuInv) 4096 a0

@[expose] def dT (_ : Unit := ()) : List (List Nat × Array Nat × Array Nat) :=
  closureTr keyD (fun g s => s.map (appN g)) (saGens.zip saInv) 200 d0

@[expose] def compGens (c : Nat) : List (Array Nat) :=
  (List.range 5).map fun i => if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!

@[expose] def colPts (s : Array Nat) : List Nat :=
  let S := spanList d0
  let im := (List.range 4096).map fun n => appN s n ^^^ n
  S.filter fun e => e != 0 && !q0b e && e != a0 && e != theta0N a0 &&
    e != (a0 ^^^ theta0N a0) && im.contains e

@[expose] def unitaryElts (i : Nat) : List (Array Nat) :=
  (compOf i).filter fun s => s != idR && unitaryN s

@[expose] def compAll (_ : Unit := ()) : List (List (Array Nat)) := (List.range 32).map compOf

@[expose] def candGens (D : List (List Nat × Array Nat × Array Nat)) (CA : List (List (Array Nat)))
    (i : Nat) (s te tei : Array Nat) : List (List (Array Nat)) :=
  let sp := mulR (mulR tei s) te
  let ai := appN tei a0
  D.flatMap fun st =>
    if (spanList st.1).contains ai then
      let spp := mulR (mulR st.2.2 sp) st.2.1
      (List.range 32).filterMap fun c =>
        if (CA.getD c []).contains spp then
          some (compGens i ++
            conjC (mulR te st.2.1) (mulR st.2.2 tei) (compGens c) ++ [theta0R])
        else none
    else []

@[expose] def orbitOf (gens : List (Array Nat)) (p : Nat) : List Nat :=
  bfsClosure id (gens.map appN) 4096 [p] ((∅ : Std.HashSet Nat).insert p) []

@[expose] def closedCheck (gs X : List (Array Nat)) : Bool :=
  let S := Std.HashSet.ofList X
  X.all fun x => gs.all fun g => S.contains (mulR x g)

@[expose] def closureD (rep : List Nat) : List (List Nat) :=
  bfsClosure keyD (saGens.map fun r s => s.map (appN r)) 5000 [rep]
    ((∅ : Std.HashSet (List Nat)).insert (keyD rep)) []

@[expose] def pairsOK (_ : Unit := ()) : Bool :=
  gamuGens.length == gamuInv.length && saGens.length == saInv.length &&
    ((gamuGens.zip gamuInv).all fun (g, gi) =>
      gammaUN g && gammaUN gi && mulR g gi == idR && mulR gi g == idR) &&
    (saGens.zip saInv).all fun (g, gi) =>
      gammaUN g && gammaUN gi && mulR g gi == idR && mulR gi g == idR && appN g a0 == a0

@[expose, noinline] def singCoverAt (ST : List (Nat × Array Nat × Array Nat)) : Bool :=
  let H := Std.HashSet.ofList (ST.map (·.1))
  (List.range 4096).all fun n => n == 0 || q0b n || H.contains n

@[expose] def singCover (_ : Unit := ()) : Bool := singCoverAt (singT ())

@[expose, noinline] def dCoverAt (K KT : Std.HashSet (List Nat)) : Bool :=
  (lagrDFS 5 [a0] (lagrCand a0)).all fun v =>
    let kv := keyD v
    K.contains kv || KT.contains kv

@[expose] def dCover (_ : Unit := ()) : Bool :=
  dCoverAt
    (Std.HashSet.ofList ((dReps.filter (· != d0)).flatMap fun rep => (closureD rep).map keyD))
    (Std.HashSet.ofList ((dT ()).map fun st => keyD st.1))

@[expose] def compGensOK (_ : Unit := ()) : Bool :=
  (List.range 32).all fun c => (compGens c).all gammaUN

@[expose] def frameCheck (_ : Unit := ()) : Bool :=
  pairsOK () && singCover () && dCover () && compGensOK ()

@[expose] def capLoop (gens : List (Array Nat)) (cap : Nat) :
    Nat → List (Array Nat) → Std.HashSet (Array Nat) → List (Array Nat) → List (Array Nat)
  | 0, frontier, _, visited => frontier ++ visited
  | fuel + 1, frontier, seen, visited =>
    if cap < frontier.length + visited.length then frontier ++ visited
    else
      let r := bfsRound (fun x : Array Nat => x) (gens.map fun g x => mulR x g) frontier seen
      if r.1.isEmpty then frontier ++ visited
      else capLoop gens cap fuel r.1 r.2 (frontier ++ visited)

@[expose] def groupClosureCap (gens : List (Array Nat)) (cap : Nat) : List (Array Nat) :=
  capLoop gens cap (cap + 2) [idR] ((∅ : Std.HashSet (Array Nat)).insert idR) []

@[expose] def candsOf (ST : List (Nat × Array Nat × Array Nat))
    (DT : List (List Nat × Array Nat × Array Nat)) (CA : List (List (Array Nat))) (i : Nat)
    (s : Array Nat) : List (List (Array Nat)) :=
  (colPts s).flatMap fun e =>
    match ST.find? (·.1 == e) with
    | some (_, te, tei) => candGens DT CA i s te tei
    | none => []

@[expose] def closedOrbit (O : List Nat) (gens : List (Array Nat)) : Bool :=
  let H := Std.HashSet.ofList O
  O.all fun x => gens.all fun g => H.contains (appN g x)

@[expose] def orbitBad (p : Nat) (gens : List (Array Nat)) : Bool :=
  let O := orbitOf gens p
  closedOrbit O gens && 1152 % O.eraseDups.length != 0

@[expose] def probe (i : Nat) : Nat := if i = 0 then 20 else 16

abbrev CensusAcc : Type :=
  List (List (Array Nat) × List (Array Nat) × Std.HashSet (Array Nat)) × Bool

@[expose] def censusStep (q : Nat) (st : CensusAcc) (gens : List (Array Nat)) : CensusAcc :=
  if st.1.any (fun p => gens.all fun g => p.2.2.contains g) then st
  else if orbitBad q gens then st
  else
    let G := groupClosureCap gens 1152
    let n := G.eraseDups.length
    if 1152 < n then st
    else if closedCheck gens G then
      if n == 1152 then (st.1 ++ [(gens, G, Std.HashSet.ofList G)], st.2)
      else st
    else (st.1, false)

@[expose] def censusOf (q : Nat) (cands : List (List (Array Nat))) : CensusAcc :=
  cands.foldl (censusStep q) ([], true)

@[expose] def rList (i : Nat) (s : Array Nat) :
    List (List (Array Nat) × List (Array Nat) × Std.HashSet (Array Nat)) :=
  (censusOf (probe i) (candsOf (singT ()) (dT ()) (compAll ()) i s)).1

@[expose, noinline] def cCheckAt (ST : List (Nat × Array Nat × Array Nat))
    (DT : List (List Nat × Array Nat × Array Nat)) (CA : List (List (Array Nat))) : Bool :=
  [0, 1].all fun i =>
    (unitaryElts i).all fun s => (censusOf (probe i) (candsOf ST DT CA i s)).2

@[expose] def cCheck (_ : Unit := ()) : Bool := cCheckAt (singT ()) (dT ()) (compAll ())

end CFSG.GammaU.Native
