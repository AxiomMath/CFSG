module

public import Certificates.Data.TwoDepSmallLow

public section

namespace Certificates.DepED4Low

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallLow

set_option compiler.extract_closed false

@[expose] def ggDepELNX : List Nat := [0, 0, 0, 0, 0, 1]

@[expose] def ggDepELNH (i : Nat) : List Nat :=
  [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0], [1, 0, 2, 0, 1, 0]].getD i []

@[expose] def ggDepELNA (i : Nat) : List Nat :=
  [[2, 0, 2, 0, 0, 0], [0, 2, 0, 2, 0, 0], [2, 0, 2, 2, 0, 0], [0, 2, 2, 2, 2, 0],
    [0, 0, 0, 2, 2, 0], [0, 0, 0, 0, 2, 0]].getD i []

@[expose] def ggDepELNZ : List Nat := [2, 1, 2, 2, 1, 0]

@[expose] def ggDepELNJ : List Nat := [1, 2, 3, 4]

@[expose] def ggDepELNLeaves : List Nat := [1, 2, 4]

@[expose] def ggDepELNInJ (c : Nat) : Bool := decide (1 ≤ c) && decide (c ≤ 4)

@[expose] def ggDepELNGen (news : List GGDepANPair) (g : Nat) : GGDepANPair :=
  if g < 6 then (ggDepELNH g, ggDepELNA g) else news.getD (g - 6) ([], [])

@[expose] def ggDepELNWord (news : List GGDepANPair) (q : GGDepANPair) (w : List Nat) :
    GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj 3 acc (ggDepELNGen news g)) q

@[expose] def ggDepELTvValid (G : Nat) (w : GGDepANWit) : Bool :=
  decide (w.g1 < G) && decide (w.g2 < G) && w.w1.all (fun g => decide (g < G)) &&
    w.w2.all fun g => decide (g < G)

@[expose] def ggDepELTvTest (news : List GGDepANPair) (w : GGDepANWit) : Bool :=
  ggDepANTestPair 3 (ggDepELNWord news (ggDepELNGen news w.g1) w.w1)
    (ggDepELNWord news (ggDepELNGen news w.g2) w.w2)

@[expose] def ggDepELSolH (tgt : Nat → Nat) : List (List Nat) :=
  (List.range (3 ^ 6)).filterMap fun k =>
    let v := ggTWNDecode 3 6 k
    if ggDepELNJ.all (fun c => ggDepANDot 3 (ggDepELNA c) v == tgt c % 3) then some v else none

@[expose] def ggDepELSolA (tgt : Nat → Nat) : List (List Nat) :=
  (List.range (3 ^ 6)).filterMap fun k =>
    let v := ggTWNDecode 3 6 k
    if ggDepELNJ.all (fun c => ggDepANDot 3 v (ggDepELNH c) == tgt c % 3) then some v else none

@[expose] def ggDepELY0One (a : List Nat) : List Nat :=
  ggDepANSub 3 ggDepELNZ
    (ggDepANSmul 3 ((ggDepANDot 3 a ggDepELNZ * ggTWLInv 3 (ggDepANDot 3 a ggDepELNX)) % 3)
      ggDepELNX)

@[expose] def ggDepELY0 (news : List GGDepANPair) : List Nat :=
  match news.find? (fun q => ggDepANDot 3 q.2 ggDepELNX % 3 != 0) with
  | some q => ggDepELY0One q.2
  | none => List.replicate 6 0

@[expose] def ggDepELNOGens (news : List GGDepANPair) : List GGDepANPair :=
  ggDepELNJ.map (fun c => (ggDepELNH c, ggDepELNA c)) ++ news

@[expose] def ggDepELHKTest (news : List GGDepANPair) (y : List Nat) (w : GGTWLHK) : Bool :=
  let og := ggDepELNOGens news
  let G := 6 + news.length
  let R := ggTWLOrbit 3 og 40 (og.map (·.1))
  let s := ggDepELNWord news (ggDepELNGen news w.g) w.w
  let v := w.ow.foldr (fun k acc => ggTWNRefl 3 (og.getD k ([], [])) acc)
    (og.getD w.oc ([], [])).1
  let sv := ggTWNRefl 3 s v
  decide (w.g < G) && w.w.all (fun g => decide (g < G)) && decide (w.oc < og.length) &&
    w.ow.all (fun k => decide (k < og.length)) &&
    ggTWLStable 3 og (og.map (·.1)) R &&
    ggDepANDot 3 s.2 y % 3 == 0 &&
    R.all fun u => !ggTWLParMod 3 y u sv

structure GGDepELPZ where
  c0 : Nat
  fixs : List (Nat × List Nat)
  orbs : List (Nat × List Nat × List Nat)
  subs : List (List (List Nat))
  cen : List Nat

@[expose] def ggDepELSubOrd (Om : List (List (List Nat))) (gs : List (List Nat)) :
    Nat × Bool :=
  let T := gs.map (ggTWLWordMat 3 6 Om)
  let par := ggTWLBfsTree 3 6 T 1000
  ((ggTWLReplay 3 6 T par).length, ggTWLEnumOK 3 6 T par)

@[expose] def ggDepELPZTest (news : List GGDepANPair) (y : List Nat) (w : GGDepELPZ) : Bool :=
  let G := 6 + news.length
  let z := ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 w.c0 y)
  let fixP : List GGDepANPair := w.fixs.map fun e => ggDepELNWord news (ggDepELNGen news e.1) e.2
  let orbP : List GGDepANPair := w.orbs.map fun e =>
    e.2.2.foldr (fun k acc => ggDepANConj 3 acc (fixP.getD k ([], [])))
      (ggDepELNWord news (ggDepELNGen news e.1) e.2.1)
  let Om := orbP.map (ggTWLMatOfPair 3 6)
  let os := w.subs.map (ggDepELSubOrd Om)
  let a := ggTWLWordMat 3 6 Om w.cen
  let cenOK := !ggTWLMatEq 3 a (ggTWLMatOne 6) &&
    Om.all fun t => ggTWLMatEq 3 (ggTWLMatMul 3 6 a t) (ggTWLMatMul 3 6 t a)
  decide (0 < w.c0) && decide (w.c0 < 3) &&
    w.fixs.all (fun e => decide (e.1 < G) && e.2.all fun g => decide (g < G)) &&
    w.orbs.all (fun e => ggDepELNInJ e.1 && e.2.1.all ggDepELNInJ &&
      e.2.2.all fun k => decide (k < fixP.length)) &&
    w.subs.all (fun gs => gs.all fun u => u.all fun j => decide (j < orbP.length)) &&
    w.cen.all (fun j => decide (j < orbP.length)) &&
    fixP.all (fun s => ggDepANDot 3 s.2 z == 0) &&
    os.all (·.2) && cenOK && ggTWLPZArith 7 (os.foldl (fun k o => Nat.lcm k o.1) 1) cenOK

inductive GGDepELReason
  | hk (w : GGTWLHK)
  | pz (w : GGDepELPZ)

@[expose] def ggDepELReasonTest (news : List GGDepANPair) : GGDepELReason → Bool
  | .hk w => ggDepELHKTest news (ggDepELY0 news) w
  | .pz w => ggDepELPZTest news (ggDepELY0 news) w

@[expose] def ggDepELCases1 (c0 : Nat) (wits : List GGDepANWit)
    (exc : List ((List Nat × List Nat) × GGDepELReason)) : Bool :=
  let has := ggDepELSolH fun c => if c = c0 then 2 else 0
  let aas := ggDepELSolA fun c => if c = c0 then 2 else 0
  has.all fun ha => aas.all fun aa =>
    if ggDepANDot 3 aa ha == 2 && ggDepANDot 3 aa ggDepELNX != 0 then
      match exc.find? (fun e => ggTWLVecEq 3 e.1.1 ha && ggTWLVecEq 3 e.1.2 aa) with
      | some e => ggDepELReasonTest [(ha, aa)] e.2
      | none => wits.any fun w => ggDepELTvTest [(ha, aa)] w
    else true

@[expose] def ggDepELCases2 (c c' : Nat) (wits : List GGDepANWit)
    (exc : List ((List Nat × List Nat × List Nat × List Nat) × GGDepELReason)) : Bool :=
  let h1s := ggDepELSolH fun d => if d = c then 2 else 0
  let a1s := ggDepELSolA fun d => if d = c then 2 else 0
  let h2s := ggDepELSolH fun d => if d = c' then 2 else 0
  let a2s := ggDepELSolA fun d => if d = c' then 2 else 0
  h1s.all fun h1 => a1s.all fun a1 =>
    if ggDepANDot 3 a1 h1 == 2 then
      h2s.all fun h2 =>
        if ggDepANDot 3 a1 h2 == 0 then
          a2s.all fun a2 =>
            if ggDepANDot 3 a2 h2 == 2 && ggDepANDot 3 a2 h1 == 0 &&
                (ggDepANDot 3 a1 ggDepELNX != 0 || ggDepANDot 3 a2 ggDepELNX != 0) &&
                (ggDepANDot 3 a1 ggDepELNX * ggDepANDot 3 a2 ggDepELNZ) % 3 ==
                  (ggDepANDot 3 a1 ggDepELNZ * ggDepANDot 3 a2 ggDepELNX) % 3 then
              match exc.find? (fun e => ggTWLVecEq 3 e.1.1 h1 && ggTWLVecEq 3 e.1.2.1 a1 &&
                  ggTWLVecEq 3 e.1.2.2.1 h2 && ggTWLVecEq 3 e.1.2.2.2 a2) with
              | some e => ggDepELReasonTest [(h1, a1), (h2, a2)] e.2
              | none => wits.any fun w => ggDepELTvTest [(h1, a1), (h2, a2)] w
            else true
        else true
    else true

structure DepELData where
  one : List (Nat × List GGDepANWit)
  two : List ((Nat × Nat) × List GGDepANWit)
  excOne : List (Nat × List ((List Nat × List Nat) × GGDepELReason))
  excTwo : List ((Nat × Nat) ×
    List ((List Nat × List Nat × List Nat × List Nat) × GGDepELReason))

@[expose] def ggDepELCheck (d : DepELData) : Bool :=
  d.one.all (fun e => e.2.all (ggDepELTvValid 7)) &&
  d.two.all (fun e => e.2.all (ggDepELTvValid 8)) &&
  ggDepELNLeaves.all (fun c0 =>
    match d.one.lookup c0 with
    | none => false
    | some wits => ggDepELCases1 c0 wits ((d.excOne.lookup c0).getD [])) &&
  ggDepELNLeaves.all fun c => ggDepELNLeaves.all fun c' =>
    if c != c' then
      match d.two.lookup (c, c') with
      | none => false
      | some wits => ggDepELCases2 c c' wits ((d.excTwo.lookup (c, c')).getD [])
    else true

@[expose] def depELData (_ : Unit := ()) : DepELData :=
  ⟨[
    (1, [
      ⟨0, [], 0, [6]⟩,
      ⟨0, [1, 3, 2], 0, [6, 1, 3, 2]⟩,
      ⟨0, [6, 4, 1, 3, 2], 1, [5, 3, 4, 2, 3]⟩,
      ⟨0, [5, 6], 2, [4, 3]⟩]),
    (2, [
      ⟨0, [], 0, [6]⟩,
      ⟨5, [], 5, [6]⟩,
      ⟨0, [6, 3, 2], 1, [4, 2, 3]⟩]),
    (4, [
      ⟨5, [], 5, [6]⟩,
      ⟨0, [], 0, [6]⟩,
      ⟨1, [6, 4, 3], 2, [5, 4, 3]⟩])],
  [
    ((1, 2), [
      ⟨0, [], 0, [7]⟩,
      ⟨5, [], 5, [7]⟩,
      ⟨0, [7, 3, 2], 1, [4, 2, 3]⟩,
      ⟨0, [], 0, [6]⟩,
      ⟨0, [0, 6, 2], 0, [7, 1, 6]⟩]),
    ((1, 4), [
      ⟨5, [], 5, [7]⟩,
      ⟨0, [], 0, [7]⟩,
      ⟨1, [7, 4, 3], 2, [5, 4, 3]⟩,
      ⟨0, [], 0, [6]⟩,
      ⟨0, [0, 6, 2], 5, [7, 1, 6]⟩]),
    ((2, 1), [
      ⟨0, [], 0, [6]⟩,
      ⟨5, [], 5, [6]⟩,
      ⟨0, [6, 3, 2], 1, [4, 2, 3]⟩,
      ⟨0, [], 0, [7]⟩,
      ⟨0, [1, 7, 2], 0, [0, 7, 6]⟩]),
    ((2, 4), [
      ⟨5, [], 5, [7]⟩,
      ⟨0, [], 0, [7]⟩,
      ⟨0, [], 0, [6]⟩,
      ⟨0, [6, 3, 2], 1, [4, 2, 3]⟩,
      ⟨5, [], 5, [6]⟩]),
    ((4, 1), [
      ⟨5, [], 5, [6]⟩,
      ⟨0, [], 0, [6]⟩,
      ⟨1, [6, 4, 3], 2, [5, 4, 3]⟩,
      ⟨0, [], 0, [7]⟩,
      ⟨0, [1, 7, 2], 5, [0, 7, 6]⟩]),
    ((4, 2), [
      ⟨0, [], 0, [7]⟩,
      ⟨5, [], 5, [6]⟩,
      ⟨0, [], 0, [6]⟩,
      ⟨0, [7, 3, 2], 1, [4, 2, 3]⟩,
      ⟨5, [], 5, [7]⟩])],
  [
    (1, [
      (([0, 2, 1, 2, 1, 1], [2, 2, 0, 0, 0, 1]), GGDepELReason.hk ⟨0, [5, 6, 4, 3, 2], 0, []⟩),
      (([0, 2, 1, 2, 1, 2], [2, 2, 0, 0, 0, 2]), GGDepELReason.hk ⟨0, [5, 6, 4, 3, 2], 0, []⟩)]),
    (2, [
      (([0, 1, 2, 2, 1, 1], [1, 0, 2, 0, 0, 1]), GGDepELReason.hk ⟨0, [5, 6], 3, []⟩),
      (([0, 1, 2, 2, 1, 2], [1, 0, 2, 0, 0, 2]), GGDepELReason.hk ⟨0, [5, 6], 3, []⟩)]),
    (4, [
      (([0, 1, 1, 2, 2, 1], [2, 0, 0, 0, 2, 1]), GGDepELReason.hk ⟨0, [5, 6], 1, []⟩),
      (([0, 1, 1, 2, 2, 2], [2, 0, 0, 0, 2, 2]), GGDepELReason.hk ⟨0, [5, 6], 1, []⟩)])],
  [
    ((1, 2), [
      (([0, 2, 1, 2, 1, 1], [2, 2, 0, 0, 0, 1], [0, 1, 2, 2, 1, 1], [1, 0, 2, 0, 0, 1]),
          GGDepELReason.pz
        ⟨1, [(0, [6])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0, 2], [4, 2, 3, 1, 0, 2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1, 4, 0], [2], [0, 2, 3,
              2, 0], [4, 1, 2, 0, 4, 3, 1, 2, 1, 4, 3, 0, 2, 1, 4], [2, 4, 3, 1, 2, 0, 4, 1, 2, 4,
              3, 2, 1, 4, 0, 2, 1, 4, 2, 3, 2, 1, 0]], [[1, 0, 2, 3, 1, 0], [4, 2, 3, 1, 2, 0, 4, 1,
              2, 4, 3, 2, 1, 0, 4, 3, 1, 2, 1, 0], [4, 3, 1, 2, 1, 0, 4, 3, 1, 2, 1, 0, 4, 0], [1,
              2, 3, 0, 2, 1, 4, 1, 0, 2, 3, 0, 2, 1]], [[1, 0, 2, 1, 4, 3, 2, 1]]],
          [2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1, 4, 0, 2, 1, 4, 2, 3, 2, 1, 0]⟩),
      (([0, 2, 1, 2, 1, 2], [2, 2, 0, 0, 0, 2], [0, 1, 2, 2, 1, 2], [1, 0, 2, 0, 0, 2]),
          GGDepELReason.pz
        ⟨1, [(0, [5, 6])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0, 2, 3, 1, 2], [1, 2, 3, 2, 1, 0, 2], [0, 2, 0], [3, 2, 1, 0, 2, 3, 1, 0], [4, 3,
              1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]], [[2, 0], [2, 1, 4, 1, 0, 2, 1, 4, 1, 0], [1,
              0, 4, 1], [3, 1, 4, 1, 0, 2, 3, 1, 0, 4, 1, 0, 2, 0]], [[0, 4, 3, 2, 1, 0, 2, 3, 2, 1,
              0, 4]]],
          [4, 3, 1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]⟩)]),
    ((1, 4), [
      (([0, 2, 1, 2, 1, 1], [2, 2, 0, 0, 0, 1], [0, 1, 1, 2, 2, 1], [2, 0, 0, 0, 2, 1]),
          GGDepELReason.pz
        ⟨1, [(0, [6])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 2, 3, 1, 2, 0], [3], [3, 1], [4, 2, 1, 4, 0, 2, 1, 4, 3, 2, 1, 4, 3, 0, 2, 1, 4],
              [4, 1, 2, 0, 4, 3, 1, 2, 1, 4, 3, 0, 2, 1, 4], [2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1,
              4, 0, 2, 1, 4, 2, 3, 2, 1, 0]], [[0, 4, 1, 2, 3, 0, 2, 4, 1, 2, 4, 3, 1, 0, 2, 1, 4,
              0], [0, 4, 1, 2, 0, 4, 3, 2, 1, 4, 2, 3, 2, 1, 0, 2, 1, 4, 1, 0], [1, 2, 3, 0, 2, 1,
              4, 1, 2, 3, 1, 0, 2, 1, 4, 2], [2, 4, 3, 1, 2, 0, 4, 1, 2, 0, 4, 3, 2, 1, 4, 2, 3,
              0]], [[0, 4, 1, 2, 4, 2, 3, 1]]],
          [2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1, 4, 0, 2, 1, 4, 2, 3, 2, 1, 0]⟩),
      (([0, 2, 1, 2, 1, 2], [2, 2, 0, 0, 0, 2], [0, 1, 1, 2, 2, 2], [2, 0, 0, 0, 2, 2]),
          GGDepELReason.pz
        ⟨1, [(0, [5, 6])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0], [1, 2, 0], [3, 1], [4, 3, 1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]], [[2, 3, 2,
              1], [2, 3, 1, 2, 1, 0, 4, 3, 0, 2, 1, 0, 4, 0], [1, 4, 1, 0, 2, 3, 2, 1, 0, 4], [1, 2,
              3, 1, 0, 4, 1, 0, 2, 3, 1, 0, 4, 0]], [[0, 2, 3, 1, 2, 4, 3, 1, 0, 4, 3, 0, 2, 1]]],
          [4, 3, 1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]⟩)]),
    ((2, 1), [
      (([0, 1, 2, 2, 1, 1], [1, 0, 2, 0, 0, 1], [0, 2, 1, 2, 1, 1], [2, 2, 0, 0, 0, 1]),
          GGDepELReason.pz
        ⟨1, [(0, [7])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0, 2], [4, 2, 3, 1, 0, 2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1, 4, 0], [2], [0, 2, 3,
              2, 0], [4, 1, 2, 0, 4, 3, 1, 2, 1, 4, 3, 0, 2, 1, 4], [2, 4, 3, 1, 2, 0, 4, 1, 2, 4,
              3, 2, 1, 4, 0, 2, 1, 4, 2, 3, 2, 1, 0]], [[1, 0, 2, 3, 1, 0], [4, 2, 3, 1, 2, 0, 4, 1,
              2, 4, 3, 2, 1, 0, 4, 3, 1, 2, 1, 0], [4, 3, 1, 2, 1, 0, 4, 3, 1, 2, 1, 0, 4, 0], [1,
              2, 3, 0, 2, 1, 4, 1, 0, 2, 3, 0, 2, 1]], [[1, 0, 2, 1, 4, 3, 2, 1]]],
          [2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1, 4, 0, 2, 1, 4, 2, 3, 2, 1, 0]⟩),
      (([0, 1, 2, 2, 1, 2], [1, 0, 2, 0, 0, 2], [0, 2, 1, 2, 1, 2], [2, 2, 0, 0, 0, 2]),
          GGDepELReason.pz
        ⟨1, [(0, [5, 7])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0, 2, 3, 1, 2], [1, 2, 3, 2, 1, 0, 2], [0, 2, 0], [3, 2, 1, 0, 2, 3, 1, 0], [4, 3,
              1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]], [[2, 0], [2, 1, 4, 1, 0, 2, 1, 4, 1, 0], [1,
              0, 4, 1], [3, 1, 4, 1, 0, 2, 3, 1, 0, 4, 1, 0, 2, 0]], [[0, 4, 3, 2, 1, 0, 2, 3, 2, 1,
              0, 4]]],
          [4, 3, 1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]⟩)]),
    ((2, 4), [
      (([0, 1, 2, 2, 1, 1], [1, 0, 2, 0, 0, 1], [0, 1, 1, 2, 2, 1], [2, 0, 0, 0, 2, 1]),
          GGDepELReason.pz
        ⟨1, [(0, [7])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (2, [], [0])],
          [[[1, 0, 2, 3, 0, 2], [1, 2, 3, 0, 2, 0], [2, 1, 0, 2, 1, 0], [1, 0, 2, 1, 0], [4, 3, 2,
              1, 4, 0, 2, 3, 2, 4, 1, 0, 2, 3, 4], [3, 2, 4, 3, 0, 2, 1, 4, 3, 2, 4, 0, 2, 3, 4, 1,
              2, 3, 4, 0, 2, 1, 0]], [[1, 0, 2, 3, 2, 1, 0, 2], [2, 4, 3, 2, 1, 4, 0, 2, 3, 4, 2, 1,
              0, 2, 3, 2, 4, 2], [2, 3, 0, 2, 4, 2, 3, 0], [1, 2, 4, 0, 2, 3, 1, 4, 2, 3, 2, 1, 0,
              2, 1, 0]], [[1, 2, 3, 4, 2, 1, 0, 2, 3, 2, 4, 1, 0, 2, 3, 0, 2, 0]]],
          [3, 2, 4, 3, 0, 2, 1, 4, 3, 2, 4, 0, 2, 3, 4, 1, 2, 3, 4, 0, 2, 1, 0]⟩),
      (([0, 1, 2, 2, 1, 2], [1, 0, 2, 0, 0, 2], [0, 1, 1, 2, 2, 2], [2, 0, 0, 0, 2, 2]),
          GGDepELReason.pz
        ⟨1, [(0, [7, 4, 3, 2])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0], [0, 2, 3, 2, 1, 0, 2, 1, 0], [1, 0, 2, 3, 2, 1, 0], [3, 2, 4, 3, 1, 2, 0, 4, 3,
              2, 4, 1, 2, 3, 4, 0, 2, 3, 4, 1, 2, 1, 0]], [[2, 1, 0, 2, 3, 2, 1, 0], [2, 4, 3, 2, 1,
              0, 2, 4, 3, 2, 4, 1, 0, 2, 3, 2, 4, 2], [3, 1, 0, 2, 4, 3, 1, 0], [4, 1, 0, 2, 3, 1,
              0, 2, 4, 3, 2, 1, 0, 2, 1, 0]], [[4, 3, 1, 2, 0, 4, 3, 2, 4, 1, 2, 3, 0, 4]]],
          [3, 2, 4, 3, 1, 2, 0, 4, 3, 2, 4, 1, 2, 3, 4, 0, 2, 3, 4, 1, 2, 1, 0]⟩)]),
    ((4, 1), [
      (([0, 1, 1, 2, 2, 1], [2, 0, 0, 0, 2, 1], [0, 2, 1, 2, 1, 1], [2, 2, 0, 0, 0, 1]),
          GGDepELReason.pz
        ⟨1, [(0, [7])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 2, 3, 1, 2, 0], [3], [3, 1], [4, 2, 1, 4, 0, 2, 1, 4, 3, 2, 1, 4, 3, 0, 2, 1, 4],
              [4, 1, 2, 0, 4, 3, 1, 2, 1, 4, 3, 0, 2, 1, 4], [2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1,
              4, 0, 2, 1, 4, 2, 3, 2, 1, 0]], [[0, 4, 1, 2, 3, 0, 2, 4, 1, 2, 4, 3, 1, 0, 2, 1, 4,
              0], [0, 4, 1, 2, 0, 4, 3, 2, 1, 4, 2, 3, 2, 1, 0, 2, 1, 4, 1, 0], [1, 2, 3, 0, 2, 1,
              4, 1, 2, 3, 1, 0, 2, 1, 4, 2], [2, 4, 3, 1, 2, 0, 4, 1, 2, 0, 4, 3, 2, 1, 4, 2, 3,
              0]], [[0, 4, 1, 2, 4, 2, 3, 1]]],
          [2, 4, 3, 1, 2, 0, 4, 1, 2, 4, 3, 2, 1, 4, 0, 2, 1, 4, 2, 3, 2, 1, 0]⟩),
      (([0, 1, 1, 2, 2, 2], [2, 0, 0, 0, 2, 2], [0, 2, 1, 2, 1, 2], [2, 2, 0, 0, 0, 2]),
          GGDepELReason.pz
        ⟨1, [(0, [5, 7])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0], [1, 2, 0], [3, 1], [4, 3, 1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]], [[2, 3, 2,
              1], [2, 3, 1, 2, 1, 0, 4, 3, 0, 2, 1, 0, 4, 0], [1, 4, 1, 0, 2, 3, 2, 1, 0, 4], [1, 2,
              3, 1, 0, 4, 1, 0, 2, 3, 1, 0, 4, 0]], [[0, 2, 3, 1, 2, 4, 3, 1, 0, 4, 3, 0, 2, 1]]],
          [4, 3, 1, 2, 0, 4, 3, 1, 2, 0, 4, 3, 1, 2, 0]⟩)]),
    ((4, 2), [
      (([0, 1, 1, 2, 2, 1], [2, 0, 0, 0, 2, 1], [0, 1, 2, 2, 1, 1], [1, 0, 2, 0, 0, 1]),
          GGDepELReason.pz
        ⟨1, [(0, [6])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (2, [], [0])],
          [[[1, 0, 2, 3, 0, 2], [1, 2, 3, 0, 2, 0], [2, 1, 0, 2, 1, 0], [1, 0, 2, 1, 0], [4, 3, 2,
              1, 4, 0, 2, 3, 2, 4, 1, 0, 2, 3, 4], [3, 2, 4, 3, 0, 2, 1, 4, 3, 2, 4, 0, 2, 3, 4, 1,
              2, 3, 4, 0, 2, 1, 0]], [[1, 0, 2, 3, 2, 1, 0, 2], [2, 4, 3, 2, 1, 4, 0, 2, 3, 4, 2, 1,
              0, 2, 3, 2, 4, 2], [2, 3, 0, 2, 4, 2, 3, 0], [1, 2, 4, 0, 2, 3, 1, 4, 2, 3, 2, 1, 0,
              2, 1, 0]], [[1, 2, 3, 4, 2, 1, 0, 2, 3, 2, 4, 1, 0, 2, 3, 0, 2, 0]]],
          [3, 2, 4, 3, 0, 2, 1, 4, 3, 2, 4, 0, 2, 3, 4, 1, 2, 3, 4, 0, 2, 1, 0]⟩),
      (([0, 1, 1, 2, 2, 2], [2, 0, 0, 0, 2, 2], [0, 1, 2, 2, 1, 2], [1, 0, 2, 0, 0, 2]),
          GGDepELReason.pz
        ⟨1, [(0, [6, 4, 3, 2])],
          [(1, [], []), (2, [], []), (3, [], []), (4, [], []), (1, [], [0])],
          [[[1, 0], [0, 2, 3, 2, 1, 0, 2, 1, 0], [1, 0, 2, 3, 2, 1, 0], [3, 2, 4, 3, 1, 2, 0, 4, 3,
              2, 4, 1, 2, 3, 4, 0, 2, 3, 4, 1, 2, 1, 0]], [[2, 1, 0, 2, 3, 2, 1, 0], [2, 4, 3, 2, 1,
              0, 2, 4, 3, 2, 4, 1, 0, 2, 3, 2, 4, 2], [3, 1, 0, 2, 4, 3, 1, 0], [4, 1, 0, 2, 3, 1,
              0, 2, 4, 3, 2, 1, 0, 2, 1, 0]], [[4, 3, 1, 2, 0, 4, 3, 2, 4, 1, 2, 3, 0, 4]]],
          [3, 2, 4, 3, 1, 2, 0, 4, 3, 2, 4, 1, 2, 3, 4, 0, 2, 3, 4, 1, 2, 1, 0]⟩)])]⟩

end Certificates.DepED4Low

end
