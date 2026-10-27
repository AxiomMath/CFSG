module

public import Certificates.Data.TwoDepSmall

public section

namespace Certificates.TwoDepSmallLow

open Certificates.DepASmall Certificates.TwoDepSmall

set_option compiler.extract_closed false

@[expose] def ggTWLVecEq (p : Nat) (u v : List Nat) : Bool :=
  decide (u.length = v.length) && (List.zipWith (fun a b => a % p == b % p) u v).all id

@[expose] def ggTWLBasis (d k : Nat) : List Nat :=
  (List.range d).map fun j => if j = k then 1 else 0

@[expose] def ggTWLMatOfPair (p d : Nat) (q : GGDepANPair) : List (List Nat) :=
  (List.range d).map fun k => ggTWNRefl p q (ggTWLBasis d k)

@[expose] def ggTWLMatApply (p d : Nat) (A : List (List Nat)) (v : List Nat) : List Nat :=
  (List.zip v A).foldl (fun acc t => ggTWNAdd p acc (ggDepANSmul p t.1 t.2)) (List.replicate d 0)

@[expose] def ggTWLMatMul (p d : Nat) (A B : List (List Nat)) : List (List Nat) :=
  B.map fun col => ggTWLMatApply p d A col

@[expose] def ggTWLMatOne (d : Nat) : List (List Nat) := (List.range d).map (ggTWLBasis d)

@[expose] def ggTWLMatEq (p : Nat) (A B : List (List Nat)) : Bool :=
  decide (A.length = B.length) && (List.zipWith (ggTWLVecEq p) A B).all id

@[expose] def ggTWLReplay (p d : Nat) (T : List (List (List Nat))) (par : List (Nat × Nat)) :
    List (List (List Nat)) :=
  par.foldl (fun L e => L ++ [ggTWLMatMul p d (L.getD e.1 []) (T.getD e.2 [])]) [ggTWLMatOne d]

@[expose] def ggTWLNodup (p : Nat) : List (List (List Nat)) → Bool
  | [] => true
  | a :: l => l.all (fun b => !ggTWLMatEq p a b) && ggTWLNodup p l

@[expose] def ggTWLEnumOK (p d : Nat) (T : List (List (List Nat))) (par : List (Nat × Nat)) :
    Bool :=
  let L := ggTWLReplay p d T par
  (List.range par.length).all (fun i => decide ((par.getD i (0, 0)).1 < i + 1) &&
      decide ((par.getD i (0, 0)).2 < T.length)) &&
    L.all (fun a => T.all fun t => L.any fun b => ggTWLMatEq p b (ggTWLMatMul p d a t)) &&
    ggTWLNodup p L

@[expose] def ggTWLBfsTree (p d : Nat) (T : List (List (List Nat))) (cap : Nat) :
    List (Nat × Nat) :=
  let st := (List.range cap).foldl (fun (st : List (List (List Nat)) × List (Nat × Nat)) i =>
    if i < st.1.length then
      (List.range T.length).foldl (fun (st2 : List (List (List Nat)) × List (Nat × Nat)) j =>
        let b := ggTWLMatMul p d (st2.1.getD i []) (T.getD j [])
        if st2.1.any (ggTWLMatEq p b) then st2 else (st2.1 ++ [b], st2.2 ++ [(i, j)])) st
    else st) ([ggTWLMatOne d], [])
  st.2


@[expose] def ggTWLInv (p a : Nat) : Nat :=
  ((List.range p).find? fun k => decide (0 < k) && (k * a) % p == 1).getD 0

@[expose] def ggTWLY0One (p N pos : Nat) (a : List Nat) : List Nat :=
  ggDepANSub p (ggTWNZ p N pos)
    (ggDepANSmul p ((ggDepANDot p a (ggTWNZ p N pos) * ggTWLInv p (ggDepANDot p a (ggTWNX N))) % p)
      (ggTWNX N))

@[expose] def ggTWLY0 (p N pos : Nat) (news : List GGDepANPair) : List Nat :=
  match news.find? (fun q => ggDepANDot p q.2 (ggTWNX N) % p != 0) with
  | some q => ggTWLY0One p N pos q.2
  | none => List.replicate (N - 1) 0

@[expose] def ggTWLOGens (p N pos : Nat) (news : List GGDepANPair) : List GGDepANPair :=
  ((List.range (N - 1)).filter (fun c => ggTWNInJ N pos c)).map
    (fun c => (ggTWNH p N c, ggTWNA p N c)) ++ news

@[expose] def ggTWLDedup (p : Nat) (l : List (List Nat)) : List (List Nat) :=
  l.foldl (fun acc w => if acc.any (ggTWLVecEq p w) then acc else acc ++ [w]) []

@[expose] def ggTWLOrbit (p : Nat) (og : List GGDepANPair) : Nat → List (List Nat) → List (List Nat)
  | 0, R => R
  | k + 1, R =>
    ggTWLOrbit p og k (ggTWLDedup p (R ++ R.flatMap fun u => og.map fun g => ggTWNRefl p g u))

@[expose] def ggTWLStable (p : Nat) (og : List GGDepANPair) (cs R : List (List Nat)) : Bool :=
  cs.all (fun c => R.any (ggTWLVecEq p c)) &&
    R.all fun u => og.all fun g => R.any (ggTWLVecEq p (ggTWNRefl p g u))

@[expose] def ggTWLParMod (p : Nat) (y u v : List Nat) : Bool :=
  (List.range p).any fun c => decide (c ≠ 0) && (List.range p).any fun d =>
    ggTWLVecEq p v (ggTWNAdd p (ggDepANSmul p c u) (ggDepANSmul p d y))

structure GGTWLHK where
  g : Nat
  w : List Nat
  oc : Nat
  ow : List Nat

@[expose] def ggTWLHKTest (p N pos : Nat) (news : List GGDepANPair) (y : List Nat)
    (w : GGTWLHK) : Bool :=
  let og := ggTWLOGens p N pos news
  let G := N - 1 + news.length
  let R := ggTWLOrbit p og 40 (og.map (·.1))
  let s := ggTWNWord p N news (ggTWNGen p N news w.g) w.w
  let v := w.ow.foldr (fun k acc => ggTWNRefl p (og.getD k ([], [])) acc) (og.getD w.oc ([], [])).1
  let sv := ggTWNRefl p s v
  decide (w.g < G) && w.w.all (fun g => decide (g < G)) && decide (w.oc < og.length) &&
    w.ow.all (fun k => decide (k < og.length)) &&
    ggTWLStable p og (og.map (·.1)) R &&
    ggDepANDot p s.2 y % p == 0 &&
    R.all fun u => !ggTWLParMod p y u sv


@[expose] def ggTWLGenMats (p N : Nat) (news : List GGDepANPair) : List (List (List Nat)) :=
  ((List.range (N - 1 + news.length)).map fun g => ggTWNGen p N news g).map
    (ggTWLMatOfPair p (N - 1))

@[expose] def ggTWLWordMat (p d : Nat) (Ts : List (List (List Nat))) (w : List Nat) :
    List (List Nat) :=
  w.foldr (fun k acc => ggTWLMatMul p d (Ts.getD k []) acc) (ggTWLMatOne d)

@[expose] def ggTWLMatPow (p d : Nat) (A : List (List Nat)) : Nat → List (List Nat)
  | 0 => ggTWLMatOne d
  | k + 1 => ggTWLMatMul p d A (ggTWLMatPow p d A k)

@[expose] def ggTWLFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * ggTWLFact n

@[expose] def ggTWLWeylTypes (r : Nat) : List (Nat × Nat) :=
  (if 1 ≤ r then [(ggTWLFact (r + 1), if r = 1 then 2 else 1)] else []) ++
  (if 2 ≤ r then [(2 ^ r * ggTWLFact r, 2)] else []) ++
  (if 4 ≤ r then [(2 ^ (r - 1) * ggTWLFact r, if r % 2 = 0 then 2 else 1)] else []) ++
  (if r = 6 then [(51840, 1)] else []) ++ (if r = 7 then [(2903040, 2)] else []) ++
  (if r = 8 then [(696729600, 2)] else []) ++ (if r = 4 then [(1152, 2)] else []) ++
  (if r = 2 then [(12, 2)] else [])

@[expose] def ggTWLPZArith (N K : Nat) (hasCen : Bool) : Bool :=
  decide (0 < K) && (List.range 3).all fun i => (ggTWLWeylTypes (N - 3 + i)).all fun t =>
    t.1 % K != 0 || (t.1 == K && t.2 == 1 && hasCen)

structure GGTWLPZ where
  c0 : Nat
  fixs : List (Nat × List Nat)
  orbs : List (Nat × List Nat × List Nat)
  hg : List Nat

@[expose] def ggTWLPZTest (p N pos : Nat) (news : List GGDepANPair) (y : List Nat)
    (w : GGTWLPZ) : Bool :=
  let d := N - 1
  let G := N - 1 + news.length
  let z := ggTWNAdd p (ggTWNX N) (ggDepANSmul p w.c0 y)
  let fixP : List GGDepANPair := w.fixs.map fun e => ggTWNWord p N news (ggTWNGen p N news e.1) e.2
  let orbP : List GGDepANPair := w.orbs.map fun e =>
    e.2.2.foldr (fun k acc => ggDepANConj p acc (fixP.getD k ([], [])))
      (ggTWNWord p N news (ggTWNGen p N news e.1) e.2.1)
  let T := (w.hg.map fun j => orbP.getD j ([], [])).map (ggTWLMatOfPair p d)
  let par := ggTWLBfsTree p d T 1000
  let Ms := ggTWLReplay p d T par
  decide (0 < w.c0) && decide (w.c0 < p) &&
    w.fixs.all (fun e => decide (e.1 < G) && e.2.all fun g => decide (g < G)) &&
    w.orbs.all (fun e => ggTWNInJ N pos e.1 && e.2.1.all (fun g => ggTWNInJ N pos g) &&
      e.2.2.all fun k => decide (k < fixP.length)) &&
    w.hg.all (fun j => decide (j < orbP.length)) &&
    fixP.all (fun s => ggDepANDot p s.2 z % p == 0) &&
    ggTWLEnumOK p d T par &&
    ggTWLPZArith N Ms.length
      (Ms.any fun a => !ggTWLMatEq p a (ggTWLMatOne d) &&
        T.all fun t => ggTWLMatEq p (ggTWLMatMul p d a t) (ggTWLMatMul p d t a))

@[expose] def ggTWLCartanE (p i j : Nat) : Nat :=
  if i = j then 2 % p
  else if (i = 0 && j = 2) || (j = 0 && i = 2) || (i = 1 && j = 3) || (j = 1 && i = 3) ||
      (2 ≤ i && i + 1 = j) || (2 ≤ j && j + 1 = i) then (p - 1) % p else 0

@[expose] def ggTWLE6M (i j : Nat) : Nat :=
  if i = j then 1
  else if (i, j) ∈ [(0, 2), (2, 0), (1, 3), (3, 1), (2, 3), (3, 2), (3, 4), (4, 3), (4, 5), (5, 4)]
    then 3 else 2

structure GGTWLE8 where
  e : List GGDepANPair
  gw : List (List Nat)
  sw : List (List Nat)

@[expose] def ggTWLE8Test (p N : Nat) (news : List GGDepANPair) (w : GGTWLE8) : Bool :=
  let d := N - 1
  let G := N - 1 + news.length
  let Tg := ggTWLGenMats p N news
  let Te := w.e.map (ggTWLMatOfPair p d)
  decide (w.e.length = 8) && decide (w.gw.length = G) && decide (w.sw.length = 8) &&
    w.e.all (fun q => decide (q.1.length = d) && decide (q.2.length = d)) &&
    (List.range 8).all (fun i => (List.range 8).all fun j =>
      ggDepANDot p (w.e.getD i ([], [])).2 (w.e.getD j ([], [])).1 % p == ggTWLCartanE p i j) &&
    w.gw.all (fun u => u.all fun k => decide (k < 8)) &&
    w.sw.all (fun u => u.all fun k => decide (k < G)) &&
    (List.range G).all (fun g =>
      ggTWLMatEq p (Tg.getD g []) (ggTWLWordMat p d Te (w.gw.getD g []))) &&
    (List.range 8).all fun i =>
      ggTWLMatEq p (Te.getD i []) (ggTWLWordMat p d Tg (w.sw.getD i []))

structure GGTWLE6 where
  s : List GGDepANPair
  gw : List (List Nat)
  sw : List (List Nat)
  ot : List (Nat × Nat)

@[expose] def ggTWLOrbitPts (p N : Nat) (news : List GGDepANPair) (ot : List (Nat × Nat)) :
    List (List Nat) :=
  ot.foldl (fun L e =>
    L ++ [ggTWNRefl p (ggTWNGen p N news e.2) (L.getD e.1 [])]) [ggTWNX N]

@[expose] def ggTWLFrameMats (p N : Nat) : List (List (List Nat)) :=
  (List.range (N - 1)).map fun g => ggTWLMatOfPair p (N - 1) (ggTWNH p N g, ggTWNA p N g)

@[expose] def ggTWLFrameOK (p N : Nat) : Bool :=
  let T := ggTWLFrameMats p N
  let par := ggTWLBfsTree p (N - 1) T 1000
  decide (720 ≤ (ggTWLReplay p (N - 1) T par).length) && ggTWLEnumOK p (N - 1) T par

@[expose] def ggTWLE6Test (p N : Nat) (news : List GGDepANPair) (w : GGTWLE6) : Bool :=
  let d := N - 1
  let G := N - 1 + news.length
  let Tg := ggTWLGenMats p N news
  let Ts := w.s.map (ggTWLMatOfPair p d)
  let V := ggTWLOrbitPts p N news w.ot
  decide (w.s.length = 6) && decide (w.gw.length = G) && decide (w.sw.length = 6) &&
    decide (w.ot.length = 71) &&
    w.s.all (fun q => decide (q.1.length = d) && decide (q.2.length = d) &&
      ggDepANDot p q.2 q.1 % p == 2 % p) &&
    w.gw.all (fun u => u.all fun k => decide (k < 6)) &&
    w.sw.all (fun u => u.all fun k => decide (k < G)) &&
    w.ot.all (fun e => decide (e.2 < G)) &&
    (List.range 6).all (fun i =>
      ggTWLMatEq p (Ts.getD i []) (ggTWLWordMat p d Tg (w.sw.getD i []))) &&
    (List.range G).all (fun g =>
      ggTWLMatEq p (Tg.getD g []) (ggTWLWordMat p d Ts (w.gw.getD g []))) &&
    (List.range 6).all (fun i => (List.range 6).all fun j =>
      ggTWLMatEq p (ggTWLMatPow p d (ggTWLMatMul p d (Ts.getD i []) (Ts.getD j []))
        (ggTWLE6M i j)) (ggTWLMatOne d)) &&
    ((List.range w.ot.length).all fun k => decide ((w.ot.getD k (0, 0)).1 < k + 1)) &&
    ggTWLNodup p (V.map fun v => [v])


inductive GGTWLReason
  | hk (w : GGTWLHK)
  | pz (w : GGTWLPZ)
  | out6 (w : GGTWLE6)
  | out8 (w : GGTWLE8)

@[expose] def ggTWLReasonTest (p N pos allow : Nat) (news : List GGDepANPair) :
    GGTWLReason → Bool
  | .hk w => ggTWLHKTest p N pos news (ggTWLY0 p N pos news) w
  | .pz w => ggTWLPZTest p N pos news (ggTWLY0 p N pos news) w
  | .out6 w => allow == 6 && ggTWLE6Test p N news w
  | .out8 w => allow == 8 && ggTWLE8Test p N news w

@[expose] def ggTWLCases1 (p N pos allow c0 mi ni : Nat) (R : List (List Nat))
    (wits : List GGTWNKill) (exc : List ((List Nat × List Nat) × GGTWLReason)) : Bool :=
  let X := ggTWNX N
  let has := ggTWNSolH p N pos fun c => if c = c0 then (p - ni % p) % p else 0
  let aas := ggTWNSolA p N pos fun c => if c = c0 then (p - mi % p) % p else 0
  has.all fun ha => aas.all fun aa =>
    if ggDepANDot p aa ha == 2 % p && ggDepANDot p aa X != 0 then
      match exc.find? (fun e => ggTWLVecEq p e.1.1 ha && ggTWLVecEq p e.1.2 aa) with
      | some e => ggTWLReasonTest p N pos allow [(ha, aa)] e.2
      | none => wits.any fun w => ggTWNKillTest p N [(ha, aa)] R w
    else true

@[expose] def ggTWLCases2 (p N pos allow c : Nat) (c2 : Option Nat) (R : List (List Nat))
    (wits : List GGTWNKill)
    (exc : List ((List Nat × List Nat × List Nat × List Nat) × GGTWLReason)) : Bool :=
  let X := ggTWNX N
  let Z := ggTWNZ p N pos
  let nb := match c2 with | none => (p - 1) % p | some _ => 0
  let h1s := ggTWNSolH p N pos fun c' => if c' = c then (p - 1) % p else 0
  let a1s := ggTWNSolA p N pos fun c' => if c' = c then (p - 1) % p else 0
  let h2s := ggTWNSolH p N pos (ggTWNTgt2 p c2)
  let a2s := ggTWNSolA p N pos (ggTWNTgt2 p c2)
  h1s.all fun h1 => a1s.all fun a1 =>
    if ggDepANDot p a1 h1 == 2 % p then
      h2s.all fun h2 =>
        if ggDepANDot p a1 h2 == nb then
          a2s.all fun a2 =>
            if ggDepANDot p a2 h2 == 2 % p && ggDepANDot p a2 h1 == nb &&
                (ggDepANDot p a1 X != 0 || ggDepANDot p a2 X != 0) &&
                (ggDepANDot p a1 X * ggDepANDot p a2 Z) % p ==
                  (ggDepANDot p a1 Z * ggDepANDot p a2 X) % p then
              match exc.find? (fun e => ggTWLVecEq p e.1.1 h1 && ggTWLVecEq p e.1.2.1 a1 &&
                  ggTWLVecEq p e.1.2.2.1 h2 && ggTWLVecEq p e.1.2.2.2 a2) with
              | some e => ggTWLReasonTest p N pos allow [(h1, a1), (h2, a2)] e.2
              | none => wits.any fun w => ggTWNKillTest p N [(h1, a1), (h2, a2)] R w
            else true
        else true
    else true

structure GGTWLData where
  one : List ((Nat × Nat × Nat × Nat) × List GGTWNKill)
  two : List ((Nat × Nat × Nat) × List GGTWNKill)
  excOne : List ((Nat × Nat × Nat × Nat) × List ((List Nat × List Nat) × GGTWLReason))
  excTwo : List ((Nat × Nat × Nat) ×
    List ((List Nat × List Nat × List Nat × List Nat) × GGTWLReason))

@[expose] def ggTWLCheck (p N allow : Nat) (d : GGTWLData) : Bool :=
  ggTWNRootsOK p N (ggTWNRoots p N) && (allow != 6 || ggTWLFrameOK p N) &&
  d.one.all (fun e => e.2.all (ggTWNKillValid N N)) &&
  d.two.all (fun e => e.2.all (ggTWNKillValid N (N + 1))) &&
  [0, 1].all fun pos =>
    ((List.range (N - 1)).all fun c0 => [1, 2].all fun mi => [1, 2].all fun ni =>
      if ggTWNPat1B N pos c0 mi ni then
        match d.one.lookup (pos, c0, mi, ni) with
        | none => false
        | some wits => ggTWLCases1 p N pos allow c0 mi ni (ggTWNRoots p N) wits
            ((d.excOne.lookup (pos, c0, mi, ni)).getD [])
      else true) &&
    ((List.range (N - 1)).all fun c => (none :: (List.range (N - 1)).map some).all fun c2 =>
      if ggTWNPat2B N pos c c2 then
        match d.two.lookup (pos, c, ggTWNCode c2) with
        | none => false
        | some wits => ggTWLCases2 p N pos allow c c2 (ggTWNRoots p N) wits
            ((d.excTwo.lookup (pos, c, ggTWNCode c2)).getD [])
      else true)

@[expose] def twDataL55 (_ : Unit := ()) : GGTWLData :=
  ⟨[
    ((0, 1, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨1, [], 1, [2, 3, 4, 3, 2]⟩,
        GGTWNKill.tv ⟨0, [], 0, [1, 4, 1]⟩, GGTWNKill.tv ⟨0, [], 4, []⟩]),
    ((0, 1, 1, 2), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨0, [], 0, [4, 1, 4]⟩,
        GGTWNKill.tv ⟨0, [], 0, [1, 4, 1]⟩, GGTWNKill.tv ⟨0, [4], 1, [0, 1, 4, 2]⟩]),
    ((0, 1, 2, 1), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨0, [], 0, [4, 1, 4]⟩,
        GGTWNKill.tv ⟨0, [], 0, [1, 4, 1]⟩, GGTWNKill.tv ⟨2, [], 3, [3, 4]⟩, GGTWNKill.tv ⟨1, [],
        3, [4]⟩]),
    ((0, 2, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩,
        GGTWNKill.tv ⟨0, [], 0, [1, 2, 4, 2, 1]⟩, GGTWNKill.tv ⟨3, [], 4, []⟩]),
    ((0, 2, 1, 2), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩,
        GGTWNKill.tv ⟨3, [], 3, [4, 2, 4]⟩, GGTWNKill.tv ⟨0, [], 2, [4]⟩, GGTWNKill.tv ⟨0, [], 0,
        [4, 1]⟩]),
    ((0, 2, 2, 1), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨3, [], 3, [4, 2, 4]⟩,
        GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩, GGTWNKill.tv ⟨0, [], 0, [4, 1]⟩, GGTWNKill.tv ⟨0, [],
        2, [4]⟩]),
    ((1, 0, 1, 1), [GGTWNKill.tv ⟨4, [], 4, [2, 3, 4, 3, 2]⟩, GGTWNKill.tv ⟨4, [], 4, [3]⟩,
        GGTWNKill.tv ⟨0, [], 1, [4, 3, 2]⟩, GGTWNKill.tv ⟨4, [], 4, [2]⟩, GGTWNKill.tv ⟨0, [], 1,
        [4, 2]⟩]),
    ((1, 0, 1, 2), [GGTWNKill.tv ⟨4, [], 4, [2, 4, 1, 2]⟩, GGTWNKill.tv ⟨3, [], 3, [4]⟩,
        GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩, GGTWNKill.tv ⟨0, [], 0, [1, 2, 4, 2, 1]⟩,
        GGTWNKill.tv ⟨0, [], 2, [4]⟩]),
    ((1, 0, 2, 1), [GGTWNKill.tv ⟨4, [], 4, [2, 4, 1, 2]⟩, GGTWNKill.tv ⟨3, [], 3, [4]⟩,
        GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩, GGTWNKill.tv ⟨0, [], 0, [1, 2, 4, 2, 1]⟩,
        GGTWNKill.tv ⟨0, [], 2, [4]⟩]),
    ((1, 1, 1, 1), [GGTWNKill.tv ⟨2, [], 2, [4]⟩, GGTWNKill.tv ⟨3, [], 3, [4]⟩, GGTWNKill.tv ⟨2,
        [], 2, [4, 3, 4]⟩, GGTWNKill.tv ⟨1, [], 1, [4, 2, 4]⟩]),
    ((1, 1, 1, 2), [GGTWNKill.tv ⟨2, [], 2, [4]⟩, GGTWNKill.tv ⟨3, [], 3, [4]⟩, GGTWNKill.tv ⟨2,
        [4], 2, [3, 4]⟩, GGTWNKill.tv ⟨2, [], 3, [3, 4]⟩]),
    ((1, 1, 2, 1), [GGTWNKill.tv ⟨2, [], 2, [4]⟩, GGTWNKill.tv ⟨3, [], 3, [4]⟩, GGTWNKill.tv ⟨2,
        [4], 2, [3, 4]⟩, GGTWNKill.tv ⟨2, [], 3, [3, 4]⟩])],
  [
    ((0, 1, 3), [GGTWNKill.tv ⟨3, [], 3, [5, 0, 5]⟩, GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩,
        GGTWNKill.tv ⟨1, [], 2, [4, 3, 0, 5]⟩, GGTWNKill.line ⟨3, [5, 4], 0, []⟩, GGTWNKill.tv ⟨2,
        [], 2, [5, 3, 5]⟩, GGTWNKill.tv ⟨0, [], 0, [1, 4, 1]⟩, GGTWNKill.tv ⟨0, [3, 2, 1], 1, [5,
        4, 2]⟩]),
    ((0, 1, 0), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨5, [], 5, [0]⟩,
        GGTWNKill.tv ⟨0, [], 0, [4, 5, 4]⟩, GGTWNKill.tv ⟨4, [], 4, [3, 5, 3]⟩, GGTWNKill.tv ⟨0,
        [], 0, [1, 4, 1]⟩, GGTWNKill.tv ⟨0, [], 4, []⟩, GGTWNKill.tv ⟨1, [], 4, [4, 5, 3]⟩]),
    ((0, 2, 2), [GGTWNKill.tv ⟨3, [], 3, [5, 0, 5]⟩, GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩,
        GGTWNKill.tv ⟨0, [], 0, [1, 5, 1]⟩, GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩, GGTWNKill.tv ⟨1,
        [], 2, [5, 3, 0, 4]⟩, GGTWNKill.line ⟨0, [5, 4], 0, []⟩, GGTWNKill.tv ⟨0, [3, 2, 1], 1,
        [5, 4, 2]⟩]),
    ((0, 2, 0), [GGTWNKill.tv ⟨0, [], 0, [4, 3, 4]⟩, GGTWNKill.tv ⟨5, [], 5, [0]⟩,
        GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩, GGTWNKill.tv ⟨4, [], 4, [0, 5, 0]⟩, GGTWNKill.tv ⟨3,
        [], 3, [4, 5, 4]⟩, GGTWNKill.tv ⟨3, [], 4, []⟩, GGTWNKill.tv ⟨2, [], 4, [4, 5, 0]⟩]),
    ((1, 0, 2), [GGTWNKill.tv ⟨4, [], 4, [2, 4, 1, 2]⟩, GGTWNKill.tv ⟨3, [], 3, [4]⟩,
        GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩, GGTWNKill.tv ⟨2, [], 2, [5]⟩, GGTWNKill.tv ⟨3, [], 3,
        [5]⟩, GGTWNKill.line ⟨5, [4, 2, 3], 0, []⟩, GGTWNKill.tv ⟨3, [], 3, [5, 2, 5]⟩]),
    ((1, 0, 0), [GGTWNKill.tv ⟨5, [], 5, [3]⟩, GGTWNKill.tv ⟨5, [3], 5, [4, 3]⟩, GGTWNKill.tv ⟨4,
        [], 4, [5, 2, 5]⟩, GGTWNKill.tv ⟨4, [], 4, [2, 4, 1, 2]⟩, GGTWNKill.tv ⟨4, [], 4, [3, 2,
        4, 2, 3]⟩, GGTWNKill.tv ⟨4, [], 4, [5, 3, 5]⟩, GGTWNKill.tv ⟨0, [], 1, [4, 3, 2]⟩]),
    ((1, 1, 1), [GGTWNKill.tv ⟨2, [], 2, [5]⟩, GGTWNKill.tv ⟨2, [], 2, [4]⟩, GGTWNKill.tv ⟨3, [],
        3, [4]⟩, GGTWNKill.tv ⟨2, [], 2, [3, 5, 3]⟩, GGTWNKill.tv ⟨2, [4], 2, [3, 4]⟩,
        GGTWNKill.tv ⟨1, [], 5, [4, 3, 2]⟩, GGTWNKill.tv ⟨5, [], 5, [3]⟩, GGTWNKill.line ⟨4, [5,
        2, 3], 0, []⟩]),
    ((1, 1, 0), [GGTWNKill.tv ⟨5, [], 5, [3]⟩, GGTWNKill.tv ⟨2, [], 2, [4]⟩, GGTWNKill.tv ⟨1, [],
        1, [4, 2, 3, 2, 4]⟩, GGTWNKill.tv ⟨2, [], 2, [3, 4, 3]⟩, GGTWNKill.tv ⟨3, [], 3, [4]⟩,
        GGTWNKill.line ⟨1, [4, 3, 5, 4], 0, []⟩])],
  [
    ((0, 1, 1, 1), [(([1, 3, 0, 1], [4, 0, 2, 3]), GGTWLReason.hk ⟨1, [3, 0, 4], 0, []⟩), (([1, 3,
        0, 2], [4, 0, 2, 4]), GGTWLReason.hk ⟨1, [3, 0, 4], 0, []⟩), (([1, 3, 0, 3], [4, 0, 2,
        1]), GGTWLReason.hk ⟨1, [3, 0, 4], 0, []⟩), (([1, 3, 0, 4], [4, 0, 2, 2]),
        GGTWLReason.hk ⟨1, [3, 0, 4], 0, []⟩), (([0, 1, 2, 1], [4, 0, 3, 1]), GGTWLReason.hk ⟨3,
        [3, 0, 1, 4], 2, []⟩), (([0, 1, 2, 2], [4, 0, 3, 3]), GGTWLReason.hk ⟨3, [3, 0, 1, 4], 2,
        []⟩), (([0, 1, 2, 3], [4, 0, 3, 2]), GGTWLReason.hk ⟨3, [3, 0, 1, 4], 2, []⟩), (([0, 1, 2,
        4], [4, 0, 3, 4]), GGTWLReason.hk ⟨3, [3, 0, 1, 4], 2, []⟩), (([2, 0, 3, 1], [4, 0, 1,
        1]), GGTWLReason.hk ⟨3, [0, 4, 0, 4], 1, []⟩), (([2, 0, 3, 2], [4, 0, 1, 3]),
        GGTWLReason.hk ⟨3, [0, 4, 0, 4], 1, []⟩), (([2, 0, 3, 3], [4, 0, 1, 2]),
        GGTWLReason.hk ⟨3, [0, 4, 0, 4], 1, []⟩), (([2, 0, 3, 4], [4, 0, 1, 4]),
        GGTWLReason.hk ⟨3, [0, 4, 0, 4], 1, []⟩)]),
    ((0, 1, 1, 2), [(([2, 1, 0, 1], [4, 0, 2, 4]), GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([2, 1,
        0, 2], [4, 0, 2, 2]), GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([2, 1, 0, 3], [4, 0, 2,
        3]), GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([2, 1, 0, 4], [4, 0, 2, 1]),
        GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([1, 4, 2, 1], [4, 0, 0, 3]), GGTWLReason.hk ⟨4,
        [3, 2, 0, 1], 0, []⟩), (([1, 4, 2, 2], [4, 0, 0, 4]), GGTWLReason.hk ⟨4, [3, 2, 0, 1], 0,
        []⟩), (([1, 4, 2, 3], [4, 0, 0, 1]), GGTWLReason.hk ⟨4, [3, 2, 0, 1], 0, []⟩), (([1, 4, 2,
        4], [4, 0, 0, 2]), GGTWLReason.hk ⟨4, [3, 2, 0, 1], 0, []⟩), (([3, 3, 3, 1], [4, 0, 4,
        3]), GGTWLReason.hk ⟨4, [3, 0], 1, []⟩), (([3, 3, 3, 2], [4, 0, 4, 4]), GGTWLReason.hk ⟨4,
        [3, 0], 1, []⟩), (([3, 3, 3, 3], [4, 0, 4, 1]), GGTWLReason.hk ⟨4, [3, 0], 1, []⟩), (([3,
        3, 3, 4], [4, 0, 4, 2]), GGTWLReason.hk ⟨4, [3, 0], 1, []⟩)]),
    ((0, 1, 2, 1), [(([1, 3, 0, 1], [3, 0, 4, 4]), GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([1, 3,
        0, 2], [3, 0, 4, 2]), GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([1, 3, 0, 3], [3, 0, 4,
        3]), GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([1, 3, 0, 4], [3, 0, 4, 1]),
        GGTWLReason.hk ⟨4, [3, 0, 1], 0, []⟩), (([3, 2, 1, 1], [3, 0, 0, 3]), GGTWLReason.hk ⟨4,
        [3, 2, 0, 1], 0, []⟩), (([3, 2, 1, 2], [3, 0, 0, 4]), GGTWLReason.hk ⟨4, [3, 2, 0, 1], 0,
        []⟩), (([3, 2, 1, 3], [3, 0, 0, 1]), GGTWLReason.hk ⟨4, [3, 2, 0, 1], 0, []⟩), (([3, 2, 1,
        4], [3, 0, 0, 2]), GGTWLReason.hk ⟨4, [3, 2, 0, 1], 0, []⟩), (([4, 4, 4, 1], [3, 0, 3,
        3]), GGTWLReason.hk ⟨4, [3, 0], 1, []⟩), (([4, 4, 4, 2], [3, 0, 3, 4]), GGTWLReason.hk ⟨4,
        [3, 0], 1, []⟩), (([4, 4, 4, 3], [3, 0, 3, 1]), GGTWLReason.hk ⟨4, [3, 0], 1, []⟩), (([4,
        4, 4, 4], [3, 0, 3, 2]), GGTWLReason.hk ⟨4, [3, 0], 1, []⟩)]),
    ((0, 2, 1, 1), [(([3, 1, 0, 1], [0, 4, 4, 3]), GGTWLReason.hk ⟨2, [3, 0, 4], 0, []⟩), (([3, 1,
        0, 2], [0, 4, 4, 4]), GGTWLReason.hk ⟨2, [3, 0, 4], 0, []⟩), (([3, 1, 0, 3], [0, 4, 4,
        1]), GGTWLReason.hk ⟨2, [3, 0, 4], 0, []⟩), (([3, 1, 0, 4], [0, 4, 4, 2]),
        GGTWLReason.hk ⟨2, [3, 0, 4], 0, []⟩), (([2, 4, 2, 1], [0, 4, 0, 1]), GGTWLReason.hk ⟨0,
        [3, 2, 0, 4], 2, []⟩), (([2, 4, 2, 2], [0, 4, 0, 3]), GGTWLReason.hk ⟨0, [3, 2, 0, 4], 2,
        []⟩), (([2, 4, 2, 3], [0, 4, 0, 2]), GGTWLReason.hk ⟨0, [3, 2, 0, 4], 2, []⟩), (([2, 4, 2,
        4], [0, 4, 0, 4]), GGTWLReason.hk ⟨0, [3, 2, 0, 4], 2, []⟩), (([4, 3, 3, 1], [0, 4, 3,
        1]), GGTWLReason.hk ⟨0, [3, 4, 3, 4], 0, []⟩), (([4, 3, 3, 2], [0, 4, 3, 3]),
        GGTWLReason.hk ⟨0, [3, 4, 3, 4], 0, []⟩), (([4, 3, 3, 3], [0, 4, 3, 2]),
        GGTWLReason.hk ⟨0, [3, 4, 3, 4], 0, []⟩), (([4, 3, 3, 4], [0, 4, 3, 4]),
        GGTWLReason.hk ⟨0, [3, 4, 3, 4], 0, []⟩)]),
    ((0, 2, 1, 2), [(([1, 2, 0, 1], [0, 4, 4, 4]), GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([1, 2,
        0, 2], [0, 4, 4, 2]), GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([1, 2, 0, 3], [0, 4, 4,
        3]), GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([1, 2, 0, 4], [0, 4, 4, 1]),
        GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([0, 0, 2, 1], [0, 4, 2, 3]), GGTWLReason.hk ⟨4,
        [3, 0, 1, 2], 1, []⟩), (([0, 0, 2, 2], [0, 4, 2, 4]), GGTWLReason.hk ⟨4, [3, 0, 1, 2], 1,
        []⟩), (([0, 0, 2, 3], [0, 4, 2, 1]), GGTWLReason.hk ⟨4, [3, 0, 1, 2], 1, []⟩), (([0, 0, 2,
        4], [0, 4, 2, 2]), GGTWLReason.hk ⟨4, [3, 0, 1, 2], 1, []⟩), (([2, 4, 3, 1], [0, 4, 1,
        3]), GGTWLReason.hk ⟨4, [3, 0], 0, []⟩), (([2, 4, 3, 2], [0, 4, 1, 4]), GGTWLReason.hk ⟨4,
        [3, 0], 0, []⟩), (([2, 4, 3, 3], [0, 4, 1, 1]), GGTWLReason.hk ⟨4, [3, 0], 0, []⟩), (([2,
        4, 3, 4], [0, 4, 1, 2]), GGTWLReason.hk ⟨4, [3, 0], 0, []⟩)]),
    ((0, 2, 2, 1), [(([3, 1, 0, 1], [0, 3, 3, 4]), GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([3, 1,
        0, 2], [0, 3, 3, 2]), GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([3, 1, 0, 3], [0, 3, 3,
        3]), GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([3, 1, 0, 4], [0, 3, 3, 1]),
        GGTWLReason.hk ⟨4, [3, 2, 0], 0, []⟩), (([0, 0, 1, 1], [0, 3, 4, 3]), GGTWLReason.hk ⟨4,
        [3, 0, 1, 2], 1, []⟩), (([0, 0, 1, 2], [0, 3, 4, 4]), GGTWLReason.hk ⟨4, [3, 0, 1, 2], 1,
        []⟩), (([0, 0, 1, 3], [0, 3, 4, 1]), GGTWLReason.hk ⟨4, [3, 0, 1, 2], 1, []⟩), (([0, 0, 1,
        4], [0, 3, 4, 2]), GGTWLReason.hk ⟨4, [3, 0, 1, 2], 1, []⟩), (([1, 2, 4, 1], [0, 3, 2,
        3]), GGTWLReason.hk ⟨4, [3, 0], 0, []⟩), (([1, 2, 4, 2], [0, 3, 2, 4]), GGTWLReason.hk ⟨4,
        [3, 0], 0, []⟩), (([1, 2, 4, 3], [0, 3, 2, 1]), GGTWLReason.hk ⟨4, [3, 0], 0, []⟩), (([1,
        2, 4, 4], [0, 3, 2, 2]), GGTWLReason.hk ⟨4, [3, 0], 0, []⟩)]),
    ((1, 0, 1, 1), [(([1, 2, 0, 1], [0, 3, 3, 1]), GGTWLReason.hk ⟨4, [2, 3], 0, []⟩), (([1, 2, 0,
        2], [0, 3, 3, 3]), GGTWLReason.hk ⟨4, [2, 3], 0, []⟩), (([1, 2, 0, 3], [0, 3, 3, 2]),
        GGTWLReason.hk ⟨4, [2, 3], 0, []⟩), (([1, 2, 0, 4], [0, 3, 3, 4]), GGTWLReason.hk ⟨4, [2,
        3], 0, []⟩), (([1, 2, 1, 1], [0, 2, 0, 3]), GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩),
        (([1, 2, 1, 2], [0, 2, 0, 4]), GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([1, 2, 1, 3],
        [0, 2, 0, 1]), GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([1, 2, 1, 4], [0, 2, 0, 2]),
        GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([1, 2, 2, 1], [0, 1, 2, 1]),
        GGTWLReason.hk ⟨2, [3, 4], 0, []⟩), (([1, 2, 2, 2], [0, 1, 2, 3]), GGTWLReason.hk ⟨2, [3,
        4], 0, []⟩), (([1, 2, 2, 3], [0, 1, 2, 2]), GGTWLReason.hk ⟨2, [3, 4], 0, []⟩), (([1, 2,
        2, 4], [0, 1, 2, 4]), GGTWLReason.hk ⟨2, [3, 4], 0, []⟩)]),
    ((1, 0, 1, 2), [(([2, 4, 1, 1], [0, 0, 4, 3]), GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([2,
        4, 1, 2], [0, 0, 4, 4]), GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([2, 4, 1, 3], [0, 0,
        4, 1]), GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([2, 4, 1, 4], [0, 0, 4, 2]),
        GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([2, 4, 2, 1], [0, 2, 0, 4]),
        GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([2, 4, 2, 2], [0, 2, 0, 2]),
        GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([2, 4, 2, 3], [0, 2, 0, 3]),
        GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([2, 4, 2, 4], [0, 2, 0, 1]),
        GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([2, 4, 3, 1], [0, 4, 1, 3]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩), (([2, 4, 3, 2], [0, 4, 1, 4]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩), (([2, 4, 3, 3], [0, 4, 1, 1]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩), (([2, 4, 3, 4], [0, 4, 1, 2]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩)]),
    ((1, 0, 2, 1), [(([1, 2, 1, 1], [0, 4, 0, 4]), GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([1,
        2, 1, 2], [0, 4, 0, 2]), GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([1, 2, 1, 3], [0, 4,
        0, 3]), GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([1, 2, 1, 4], [0, 4, 0, 1]),
        GGTWLReason.hk ⟨4, [2, 3, 1, 2], 0, []⟩), (([1, 2, 3, 1], [0, 0, 3, 3]),
        GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([1, 2, 3, 2], [0, 0, 3, 4]),
        GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([1, 2, 3, 3], [0, 0, 3, 1]),
        GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([1, 2, 3, 4], [0, 0, 3, 2]),
        GGTWLReason.hk ⟨0, [3, 4, 2, 1], 0, []⟩), (([1, 2, 4, 1], [0, 3, 2, 3]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩), (([1, 2, 4, 2], [0, 3, 2, 4]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩), (([1, 2, 4, 3], [0, 3, 2, 1]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩), (([1, 2, 4, 4], [0, 3, 2, 2]),
        GGTWLReason.hk ⟨0, [2, 3, 4, 1], 0, []⟩)]),
    ((1, 1, 1, 1), [(([0, 1, 2, 1], [4, 0, 3, 1]), GGTWLReason.hk ⟨1, [3, 4, 2], 0, []⟩), (([0, 1,
        2, 2], [4, 0, 3, 3]), GGTWLReason.hk ⟨1, [3, 4, 2], 0, []⟩), (([0, 1, 2, 3], [4, 0, 3,
        2]), GGTWLReason.hk ⟨1, [3, 4, 2], 0, []⟩), (([0, 1, 2, 4], [4, 0, 3, 4]),
        GGTWLReason.hk ⟨1, [3, 4, 2], 0, []⟩), (([0, 1, 3, 1], [4, 4, 0, 3]), GGTWLReason.hk ⟨0,
        [2, 3, 1, 2, 4, 1], 0, []⟩), (([0, 1, 3, 2], [4, 4, 0, 4]), GGTWLReason.hk ⟨0, [2, 3, 1,
        2, 4, 1], 0, []⟩), (([0, 1, 3, 3], [4, 4, 0, 1]), GGTWLReason.hk ⟨0, [2, 3, 1, 2, 4, 1],
        0, []⟩), (([0, 1, 3, 4], [4, 4, 0, 2]), GGTWLReason.hk ⟨0, [2, 3, 1, 2, 4, 1], 0, []⟩),
        (([0, 1, 4, 1], [4, 3, 2, 1]), GGTWLReason.hk ⟨3, [2, 4], 2, []⟩), (([0, 1, 4, 2], [4, 3,
        2, 3]), GGTWLReason.hk ⟨3, [2, 4], 2, []⟩), (([0, 1, 4, 3], [4, 3, 2, 2]),
        GGTWLReason.hk ⟨3, [2, 4], 2, []⟩), (([0, 1, 4, 4], [4, 3, 2, 4]), GGTWLReason.hk ⟨3, [2,
        4], 2, []⟩)]),
    ((1, 1, 1, 2), [(([0, 2, 0, 1], [4, 2, 4, 3]), GGTWLReason.hk ⟨4, [3, 2], 1, []⟩), (([0, 2, 0,
        2], [4, 2, 4, 4]), GGTWLReason.hk ⟨4, [3, 2], 1, []⟩), (([0, 2, 0, 3], [4, 2, 4, 1]),
        GGTWLReason.hk ⟨4, [3, 2], 1, []⟩), (([0, 2, 0, 4], [4, 2, 4, 2]), GGTWLReason.hk ⟨4, [3,
        2], 1, []⟩), (([0, 2, 1, 1], [4, 4, 0, 4]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩),
        (([0, 2, 1, 2], [4, 4, 0, 2]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩), (([0, 2, 1,
        3], [4, 4, 0, 3]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩), (([0, 2, 1, 4], [4, 4, 0,
        1]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩), (([0, 2, 2, 1], [4, 1, 1, 3]),
        GGTWLReason.hk ⟨2, [3, 4], 1, []⟩), (([0, 2, 2, 2], [4, 1, 1, 4]), GGTWLReason.hk ⟨2, [3,
        4], 1, []⟩), (([0, 2, 2, 3], [4, 1, 1, 1]), GGTWLReason.hk ⟨2, [3, 4], 1, []⟩), (([0, 2,
        2, 4], [4, 1, 1, 2]), GGTWLReason.hk ⟨2, [3, 4], 1, []⟩)]),
    ((1, 1, 2, 1), [(([0, 1, 0, 1], [3, 4, 3, 3]), GGTWLReason.hk ⟨4, [3, 2], 1, []⟩), (([0, 1, 0,
        2], [3, 4, 3, 4]), GGTWLReason.hk ⟨4, [3, 2], 1, []⟩), (([0, 1, 0, 3], [3, 4, 3, 1]),
        GGTWLReason.hk ⟨4, [3, 2], 1, []⟩), (([0, 1, 0, 4], [3, 4, 3, 2]), GGTWLReason.hk ⟨4, [3,
        2], 1, []⟩), (([0, 1, 1, 1], [3, 2, 2, 3]), GGTWLReason.hk ⟨2, [3, 4], 1, []⟩), (([0, 1,
        1, 2], [3, 2, 2, 4]), GGTWLReason.hk ⟨2, [3, 4], 1, []⟩), (([0, 1, 1, 3], [3, 2, 2, 1]),
        GGTWLReason.hk ⟨2, [3, 4], 1, []⟩), (([0, 1, 1, 4], [3, 2, 2, 2]), GGTWLReason.hk ⟨2, [3,
        4], 1, []⟩), (([0, 1, 3, 1], [3, 3, 0, 4]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩),
        (([0, 1, 3, 2], [3, 3, 0, 2]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩), (([0, 1, 3,
        3], [3, 3, 0, 3]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩), (([0, 1, 3, 4], [3, 3, 0,
        1]), GGTWLReason.hk ⟨1, [2, 3, 1, 2, 4], 0, []⟩)])],
  [
    ((0, 1, 3), [(([1, 3, 0, 1], [4, 0, 2, 3], [3, 1, 0, 1], [0, 4, 4, 3]), GGTWLReason.pz ⟨1,
        [(4, [3])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([1, 3, 0, 2], [4, 0,
        2, 4], [3, 1, 0, 2], [0, 4, 4, 4]), GGTWLReason.pz ⟨1, [(0, [3, 4])], [(1, [], []), (2,
        [], []), (1, [], [0])], [0, 1, 2]⟩), (([1, 3, 0, 3], [4, 0, 2, 1], [3, 1, 0, 3], [0, 4, 4,
        1]), GGTWLReason.pz ⟨1, [(0, [4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([1, 3, 0, 4], [4, 0, 2, 2], [3, 1, 0, 4], [0, 4, 4, 2]), GGTWLReason.pz ⟨1, [(0, [5])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 1], [4, 0, 3, 1], [2,
        4, 2, 1], [0, 4, 0, 1]), GGTWLReason.pz ⟨2, [(0, [5])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([0, 1, 2, 2], [4, 0, 3, 3], [2, 4, 2, 2], [0, 4, 0, 3]),
        GGTWLReason.pz ⟨1, [(0, [5])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([0, 1, 2, 3], [4, 0, 3, 2], [2, 4, 2, 3], [0, 4, 0, 2]), GGTWLReason.pz ⟨1, [(4, [3])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 4], [4, 0, 3, 4], [2,
        4, 2, 4], [0, 4, 0, 4]), GGTWLReason.pz ⟨1, [(0, [0, 5])], [(1, [], []), (2, [], []), (1,
        [], [0])], [0, 1, 2]⟩), (([2, 0, 3, 1], [4, 0, 1, 1], [4, 3, 3, 1], [0, 4, 3, 1]),
        GGTWLReason.pz ⟨1, [(0, [5, 4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([2, 0, 3, 2], [4, 0, 1, 3], [4, 3, 3, 2], [0, 4, 3, 3]), GGTWLReason.pz ⟨1, [(0, [4])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([2, 0, 3, 3], [4, 0, 1, 2], [4,
        3, 3, 3], [0, 4, 3, 2]), GGTWLReason.pz ⟨1, [(4, [0])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([2, 0, 3, 4], [4, 0, 1, 4], [4, 3, 3, 4], [0, 4, 3, 4]),
        GGTWLReason.pz ⟨2, [(4, [0])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩)]),
    ((0, 1, 0), [(([1, 3, 0, 1], [4, 0, 2, 3], [0, 0, 0, 3], [0, 0, 0, 4]), GGTWLReason.pz ⟨1,
        [(4, [3])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([1, 3, 0, 2], [4, 0,
        2, 4], [0, 0, 0, 1], [0, 0, 0, 2]), GGTWLReason.pz ⟨1, [(0, [3, 4])], [(1, [], []), (2,
        [], []), (1, [], [0])], [0, 1, 2]⟩), (([1, 3, 0, 3], [4, 0, 2, 1], [0, 0, 0, 4], [0, 0, 0,
        3]), GGTWLReason.pz ⟨1, [(0, [4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([1, 3, 0, 4], [4, 0, 2, 2], [0, 0, 0, 2], [0, 0, 0, 1]), GGTWLReason.pz ⟨1, [(3, [4])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 1], [4, 0, 3, 1], [2,
        4, 1, 3], [0, 0, 3, 3]), GGTWLReason.pz ⟨2, [(3, [4])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([0, 1, 2, 2], [4, 0, 3, 3], [2, 4, 1, 1], [0, 0, 3, 4]),
        GGTWLReason.pz ⟨1, [(3, [4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([0, 1, 2, 3], [4, 0, 3, 2], [2, 4, 1, 4], [0, 0, 3, 1]), GGTWLReason.pz ⟨1, [(4, [3])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 4], [4, 0, 3, 4], [2,
        4, 1, 2], [0, 0, 3, 2]), GGTWLReason.pz ⟨1, [(5, [0])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([2, 0, 3, 1], [4, 0, 1, 1], [3, 1, 4, 3], [0, 0, 2, 3]),
        GGTWLReason.pz ⟨1, [(5, [0])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([2, 0, 3, 2], [4, 0, 1, 3], [3, 1, 4, 1], [0, 0, 2, 4]), GGTWLReason.pz ⟨1, [(0, [4])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([2, 0, 3, 3], [4, 0, 1, 2], [3,
        1, 4, 4], [0, 0, 2, 1]), GGTWLReason.pz ⟨1, [(4, [0])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([2, 0, 3, 4], [4, 0, 1, 4], [3, 1, 4, 2], [0, 0, 2, 2]),
        GGTWLReason.pz ⟨2, [(4, [0])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩)]),
    ((0, 2, 2), [(([3, 1, 0, 1], [0, 4, 4, 3], [1, 3, 0, 1], [4, 0, 2, 3]), GGTWLReason.pz ⟨1,
        [(4, [0])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([3, 1, 0, 2], [0, 4,
        4, 4], [1, 3, 0, 2], [4, 0, 2, 4]), GGTWLReason.pz ⟨1, [(0, [5, 4])], [(1, [], []), (2,
        [], []), (1, [], [0])], [0, 1, 2]⟩), (([3, 1, 0, 3], [0, 4, 4, 1], [1, 3, 0, 3], [4, 0, 2,
        1]), GGTWLReason.pz ⟨1, [(0, [5])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([3, 1, 0, 4], [0, 4, 4, 2], [1, 3, 0, 4], [4, 0, 2, 2]), GGTWLReason.pz ⟨1, [(0, [4])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([2, 4, 2, 1], [0, 4, 0, 1], [0,
        1, 2, 1], [4, 0, 3, 1]), GGTWLReason.pz ⟨2, [(0, [4])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([2, 4, 2, 2], [0, 4, 0, 3], [0, 1, 2, 2], [4, 0, 3, 3]),
        GGTWLReason.pz ⟨1, [(0, [4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([2, 4, 2, 3], [0, 4, 0, 2], [0, 1, 2, 3], [4, 0, 3, 2]), GGTWLReason.pz ⟨1, [(4, [0])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([2, 4, 2, 4], [0, 4, 0, 4], [0,
        1, 2, 4], [4, 0, 3, 4]), GGTWLReason.pz ⟨1, [(0, [0, 4])], [(1, [], []), (2, [], []), (1,
        [], [0])], [0, 1, 2]⟩), (([4, 3, 3, 1], [0, 4, 3, 1], [2, 0, 3, 1], [4, 0, 1, 1]),
        GGTWLReason.pz ⟨1, [(0, [3, 4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([4, 3, 3, 2], [0, 4, 3, 3], [2, 0, 3, 2], [4, 0, 1, 3]), GGTWLReason.pz ⟨1, [(0, [5])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([4, 3, 3, 3], [0, 4, 3, 2], [2,
        0, 3, 3], [4, 0, 1, 2]), GGTWLReason.pz ⟨1, [(5, [0])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([4, 3, 3, 4], [0, 4, 3, 4], [2, 0, 3, 4], [4, 0, 1, 4]),
        GGTWLReason.pz ⟨2, [(5, [0])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩)]),
    ((0, 2, 0), [(([3, 1, 0, 1], [0, 4, 4, 3], [0, 0, 0, 3], [0, 0, 0, 4]), GGTWLReason.pz ⟨1,
        [(4, [0])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([3, 1, 0, 2], [0, 4,
        4, 4], [0, 0, 0, 1], [0, 0, 0, 2]), GGTWLReason.pz ⟨1, [(3, [0, 4])], [(1, [], []), (2,
        [], []), (1, [], [0])], [0, 1, 2]⟩), (([3, 1, 0, 3], [0, 4, 4, 1], [0, 0, 0, 4], [0, 0, 0,
        3]), GGTWLReason.pz ⟨1, [(0, [0, 4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1,
        2]⟩), (([3, 1, 0, 4], [0, 4, 4, 2], [0, 0, 0, 2], [0, 0, 0, 1]), GGTWLReason.pz ⟨1, [(0,
        [4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([2, 4, 2, 1], [0, 4, 0,
        1], [2, 4, 1, 3], [0, 0, 3, 3]), GGTWLReason.pz ⟨2, [(0, [4])], [(1, [], []), (2, [], []),
        (1, [], [0])], [0, 1, 2]⟩), (([2, 4, 2, 2], [0, 4, 0, 3], [2, 4, 1, 1], [0, 0, 3, 4]),
        GGTWLReason.pz ⟨1, [(0, [4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([2, 4, 2, 3], [0, 4, 0, 2], [2, 4, 1, 4], [0, 0, 3, 1]), GGTWLReason.pz ⟨1, [(4, [0])],
        [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([2, 4, 2, 4], [0, 4, 0, 4], [2,
        4, 1, 2], [0, 0, 3, 2]), GGTWLReason.pz ⟨1, [(5, [0])], [(1, [], []), (2, [], []), (1, [],
        [0])], [0, 1, 2]⟩), (([4, 3, 3, 1], [0, 4, 3, 1], [3, 1, 4, 3], [0, 0, 2, 3]),
        GGTWLReason.pz ⟨1, [(5, [0])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩),
        (([4, 3, 3, 2], [0, 4, 3, 3], [3, 1, 4, 1], [0, 0, 2, 4]), GGTWLReason.pz ⟨1, [(2, [3,
        4])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩), (([4, 3, 3, 3], [0, 4, 3, 2],
        [3, 1, 4, 4], [0, 0, 2, 1]), GGTWLReason.pz ⟨1, [(0, [0, 5])], [(1, [], []), (2, [], []),
        (1, [], [0])], [0, 1, 2]⟩), (([4, 3, 3, 4], [0, 4, 3, 4], [3, 1, 4, 2], [0, 0, 2, 2]),
        GGTWLReason.pz ⟨2, [(0, [0, 5])], [(1, [], []), (2, [], []), (1, [], [0])], [0, 1, 2]⟩)]),
    ((1, 0, 2), [(([1, 2, 0, 1], [0, 3, 3, 1], [0, 1, 2, 1], [4, 0, 3, 1]), GGTWLReason.pz ⟨2,
        [(2, [4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 0, 2], [0, 3,
        3, 3], [0, 1, 2, 2], [4, 0, 3, 3]), GGTWLReason.pz ⟨1, [(2, [4])], [(0, [], []), (1, [],
        []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 0, 3], [0, 3, 3, 2], [0, 1, 2, 3], [4, 0, 3,
        2]), GGTWLReason.pz ⟨1, [(4, [2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([1, 2, 0, 4], [0, 3, 3, 4], [0, 1, 2, 4], [4, 0, 3, 4]), GGTWLReason.pz ⟨1, [(3, [4])],
        [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 1, 1], [0, 2, 0, 3], [0,
        1, 3, 1], [4, 4, 0, 3]), GGTWLReason.pz ⟨1, [(4, [2])], [(0, [], []), (1, [], []), (0, [],
        [0])], [0, 1, 2]⟩), (([1, 2, 1, 2], [0, 2, 0, 4], [0, 1, 3, 2], [4, 4, 0, 4]),
        GGTWLReason.pz ⟨1, [(2, [5, 4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([1, 2, 1, 3], [0, 2, 0, 1], [0, 1, 3, 3], [4, 4, 0, 1]), GGTWLReason.pz ⟨1, [(2, [2,
        4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 1, 4], [0, 2, 0, 2],
        [0, 1, 3, 4], [4, 4, 0, 2]), GGTWLReason.pz ⟨1, [(2, [4])], [(0, [], []), (1, [], []), (0,
        [], [0])], [0, 1, 2]⟩), (([1, 2, 2, 1], [0, 1, 2, 1], [0, 1, 4, 1], [4, 3, 2, 1]),
        GGTWLReason.pz ⟨1, [(3, [4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([1, 2, 2, 2], [0, 1, 2, 3], [0, 1, 4, 2], [4, 3, 2, 3]), GGTWLReason.pz ⟨1, [(1, [2,
        5])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 2, 3], [0, 1, 2, 2],
        [0, 1, 4, 3], [4, 3, 2, 2]), GGTWLReason.pz ⟨1, [(1, [5, 2])], [(0, [], []), (1, [], []),
        (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 2, 4], [0, 1, 2, 4], [0, 1, 4, 4], [4, 3, 2, 4]),
        GGTWLReason.pz ⟨2, [(1, [5, 2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩)]),
    ((1, 0, 0), [(([1, 2, 0, 1], [0, 3, 3, 1], [0, 0, 2, 3], [0, 3, 4, 3]), GGTWLReason.pz ⟨2,
        [(2, [4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 0, 2], [0, 3,
        3, 3], [0, 0, 2, 1], [0, 3, 4, 4]), GGTWLReason.pz ⟨1, [(2, [4])], [(0, [], []), (1, [],
        []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 0, 3], [0, 3, 3, 2], [0, 0, 2, 4], [0, 3, 4,
        1]), GGTWLReason.pz ⟨1, [(4, [2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([1, 2, 0, 4], [0, 3, 3, 4], [0, 0, 2, 2], [0, 3, 4, 2]), GGTWLReason.pz ⟨1, [(3, [4])],
        [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 1, 1], [0, 2, 0, 3], [0,
        0, 0, 3], [0, 0, 0, 4]), GGTWLReason.pz ⟨1, [(4, [2])], [(0, [], []), (1, [], []), (0, [],
        [0])], [0, 1, 2]⟩), (([1, 2, 1, 2], [0, 2, 0, 4], [0, 0, 0, 1], [0, 0, 0, 2]),
        GGTWLReason.pz ⟨1, [(0, [4, 2, 1])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1,
        2]⟩), (([1, 2, 1, 3], [0, 2, 0, 1], [0, 0, 0, 4], [0, 0, 0, 3]), GGTWLReason.pz ⟨1, [(2,
        [2, 4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 1, 4], [0, 2, 0,
        2], [0, 0, 0, 2], [0, 0, 0, 1]), GGTWLReason.pz ⟨1, [(2, [4])], [(0, [], []), (1, [], []),
        (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 2, 1], [0, 1, 2, 1], [0, 0, 3, 3], [0, 2, 1, 3]),
        GGTWLReason.pz ⟨1, [(3, [4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([1, 2, 2, 2], [0, 1, 2, 3], [0, 0, 3, 1], [0, 2, 1, 4]), GGTWLReason.pz ⟨1, [(3, [3,
        4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 2, 3], [0, 1, 2, 2],
        [0, 0, 3, 4], [0, 2, 1, 1]), GGTWLReason.pz ⟨1, [(2, [4, 3])], [(0, [], []), (1, [], []),
        (0, [], [0])], [0, 1, 2]⟩), (([1, 2, 2, 4], [0, 1, 2, 4], [0, 0, 3, 2], [0, 2, 1, 2]),
        GGTWLReason.pz ⟨2, [(2, [4, 3])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩)]),
    ((1, 1, 1), [(([0, 1, 2, 1], [4, 0, 3, 1], [1, 2, 0, 1], [0, 3, 3, 1]), GGTWLReason.pz ⟨2,
        [(2, [5])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 2], [4, 0,
        3, 3], [1, 2, 0, 2], [0, 3, 3, 3]), GGTWLReason.pz ⟨1, [(2, [5])], [(0, [], []), (1, [],
        []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 3], [4, 0, 3, 2], [1, 2, 0, 3], [0, 3, 3,
        2]), GGTWLReason.pz ⟨1, [(5, [2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([0, 1, 2, 4], [4, 0, 3, 4], [1, 2, 0, 4], [0, 3, 3, 4]), GGTWLReason.pz ⟨1, [(3, [5])],
        [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 3, 1], [4, 4, 0, 3], [1,
        2, 1, 1], [0, 2, 0, 3]), GGTWLReason.pz ⟨1, [(5, [2])], [(0, [], []), (1, [], []), (0, [],
        [0])], [0, 1, 2]⟩), (([0, 1, 3, 2], [4, 4, 0, 4], [1, 2, 1, 2], [0, 2, 0, 4]),
        GGTWLReason.pz ⟨1, [(2, [5, 4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([0, 1, 3, 3], [4, 4, 0, 1], [1, 2, 1, 3], [0, 2, 0, 1]), GGTWLReason.pz ⟨1, [(2, [1,
        4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 3, 4], [4, 4, 0, 2],
        [1, 2, 1, 4], [0, 2, 0, 2]), GGTWLReason.pz ⟨1, [(2, [5])], [(0, [], []), (1, [], []), (0,
        [], [0])], [0, 1, 2]⟩), (([0, 1, 4, 1], [4, 3, 2, 1], [1, 2, 2, 1], [0, 1, 2, 1]),
        GGTWLReason.pz ⟨1, [(3, [5])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([0, 1, 4, 2], [4, 3, 2, 3], [1, 2, 2, 2], [0, 1, 2, 3]), GGTWLReason.pz ⟨1, [(1, [2,
        4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 4, 3], [4, 3, 2, 2],
        [1, 2, 2, 3], [0, 1, 2, 2]), GGTWLReason.pz ⟨1, [(1, [4, 2])], [(0, [], []), (1, [], []),
        (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 4, 4], [4, 3, 2, 4], [1, 2, 2, 4], [0, 1, 2, 4]),
        GGTWLReason.pz ⟨2, [(1, [4, 2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩)]),
    ((1, 1, 0), [(([0, 1, 2, 1], [4, 0, 3, 1], [0, 0, 2, 3], [0, 3, 4, 3]), GGTWLReason.pz ⟨2,
        [(1, [4, 3, 2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 2],
        [4, 0, 3, 3], [0, 0, 2, 1], [0, 3, 4, 4]), GGTWLReason.pz ⟨1, [(1, [4, 3, 2])], [(0, [],
        []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 2, 3], [4, 0, 3, 2], [0, 0, 2, 4],
        [0, 3, 4, 1]), GGTWLReason.pz ⟨1, [(1, [2, 5, 4])], [(0, [], []), (1, [], []), (0, [],
        [0])], [0, 1, 2]⟩), (([0, 1, 2, 4], [4, 0, 3, 4], [0, 0, 2, 2], [0, 3, 4, 2]),
        GGTWLReason.pz ⟨1, [(3, [1, 4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩),
        (([0, 1, 3, 1], [4, 4, 0, 3], [0, 0, 0, 3], [0, 0, 0, 4]), GGTWLReason.pz ⟨1, [(1, [4,
        2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 3, 2], [4, 4, 0, 4],
        [0, 0, 0, 1], [0, 0, 0, 2]), GGTWLReason.pz ⟨1, [(2, [1, 4, 3])], [(0, [], []), (1, [],
        []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 3, 3], [4, 4, 0, 1], [0, 0, 0, 4], [0, 0, 0,
        3]), GGTWLReason.pz ⟨1, [(2, [1, 4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1,
        2]⟩), (([0, 1, 3, 4], [4, 4, 0, 2], [0, 0, 0, 2], [0, 0, 0, 1]), GGTWLReason.pz ⟨1, [(1,
        [2, 4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 4, 1], [4, 3, 2,
        1], [0, 0, 3, 3], [0, 2, 1, 3]), GGTWLReason.pz ⟨1, [(3, [1, 4])], [(0, [], []), (1, [],
        []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 4, 2], [4, 3, 2, 3], [0, 0, 3, 1], [0, 2, 1,
        4]), GGTWLReason.pz ⟨1, [(1, [2, 4])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1,
        2]⟩), (([0, 1, 4, 3], [4, 3, 2, 2], [0, 0, 3, 4], [0, 2, 1, 1]), GGTWLReason.pz ⟨1, [(1,
        [4, 2])], [(0, [], []), (1, [], []), (0, [], [0])], [0, 1, 2]⟩), (([0, 1, 4, 4], [4, 3, 2,
        4], [0, 0, 3, 2], [0, 2, 1, 2]), GGTWLReason.pz ⟨2, [(1, [4, 2])], [(0, [], []), (1, [],
        []), (0, [], [0])], [0, 1, 2]⟩)])]⟩

@[expose] def twDataL36 (_ : Unit := ()) : GGTWLData :=
  ⟨[
    ((0, 1, 1, 1), [GGTWNKill.tv ⟨5, [], 5, [0]⟩, GGTWNKill.tv ⟨5, [], 5, [4]⟩, GGTWNKill.tv ⟨1,
        [], 2, [5, 4, 3]⟩]),
    ((0, 1, 1, 2), [GGTWNKill.tv ⟨5, [], 5, [0]⟩, GGTWNKill.tv ⟨4, [], 4, [5]⟩]),
    ((0, 1, 2, 1), [GGTWNKill.tv ⟨5, [], 5, [0]⟩, GGTWNKill.tv ⟨4, [], 4, [5]⟩]),
    ((0, 2, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [5]⟩, GGTWNKill.line ⟨0, [5, 4, 2, 5], 0, []⟩]),
    ((0, 3, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [5, 4, 5]⟩, GGTWNKill.tv ⟨4, [], 5, []⟩,
        GGTWNKill.tv ⟨0, [], 1, [5, 3, 2]⟩]),
    ((0, 3, 1, 2), [GGTWNKill.tv ⟨0, [], 0, [5, 4, 5]⟩]),
    ((0, 3, 2, 1), [GGTWNKill.tv ⟨5, [], 5, [4]⟩, GGTWNKill.tv ⟨0, [], 0, [5]⟩]),
    ((1, 0, 1, 1), [GGTWNKill.tv ⟨5, [], 5, [4]⟩, GGTWNKill.tv ⟨0, [], 1, [5, 4, 3, 2]⟩,
        GGTWNKill.tv ⟨5, [], 5, [3]⟩, GGTWNKill.tv ⟨0, [], 1, [5, 3, 2]⟩]),
    ((1, 0, 1, 2), [GGTWNKill.tv ⟨5, [], 5, [4]⟩, GGTWNKill.tv ⟨3, [], 3, [5]⟩]),
    ((1, 0, 2, 1), [GGTWNKill.tv ⟨3, [], 3, [5]⟩, GGTWNKill.tv ⟨5, [], 5, [4]⟩]),
    ((1, 1, 1, 1), [GGTWNKill.tv ⟨5, [], 5, [3]⟩, GGTWNKill.tv ⟨5, [], 5, [4]⟩]),
    ((1, 2, 1, 1), [GGTWNKill.tv ⟨3, [], 3, [5]⟩, GGTWNKill.tv ⟨2, [], 2, [3, 5, 3]⟩,
        GGTWNKill.tv ⟨3, [], 4, [5]⟩]),
    ((1, 2, 1, 2), [GGTWNKill.tv ⟨3, [], 3, [5]⟩, GGTWNKill.tv ⟨3, [], 4, [5]⟩]),
    ((1, 2, 2, 1), [GGTWNKill.tv ⟨3, [], 3, [5]⟩, GGTWNKill.tv ⟨3, [], 4, [5]⟩])],
  [
    ((0, 1, 4), [GGTWNKill.tv ⟨5, [], 5, [0]⟩, GGTWNKill.tv ⟨4, [], 4, [6]⟩, GGTWNKill.tv ⟨5, [],
        6, [4, 0]⟩, GGTWNKill.tv ⟨0, [], 1, [6, 3, 2]⟩]),
    ((0, 1, 0), [GGTWNKill.tv ⟨5, [], 5, [0]⟩, GGTWNKill.tv ⟨5, [], 5, [6, 0, 6]⟩,
        GGTWNKill.tv ⟨5, [], 5, [4]⟩, GGTWNKill.tv ⟨6, [], 6, [0]⟩]),
    ((0, 3, 2), [GGTWNKill.tv ⟨0, [], 0, [6]⟩, GGTWNKill.tv ⟨0, [], 0, [5, 4, 5]⟩,
        GGTWNKill.tv ⟨4, [], 4, [6]⟩, GGTWNKill.tv ⟨0, [], 1, [5, 3, 2]⟩]),
    ((0, 3, 0), [GGTWNKill.tv ⟨5, [], 5, [6, 4, 6]⟩, GGTWNKill.tv ⟨0, [], 0, [5, 4, 5]⟩,
        GGTWNKill.tv ⟨4, [], 5, []⟩, GGTWNKill.tv ⟨6, [], 6, [0]⟩]),
    ((1, 0, 3), [GGTWNKill.tv ⟨3, [], 3, [6]⟩, GGTWNKill.line ⟨5, [6, 4], 0, []⟩, GGTWNKill.tv ⟨3,
        [], 4, [6]⟩, GGTWNKill.tv ⟨4, [], 4, [5]⟩]),
    ((1, 0, 0), [GGTWNKill.tv ⟨4, [], 4, [6]⟩, GGTWNKill.tv ⟨5, [], 5, [4]⟩, GGTWNKill.line ⟨6,
        [5, 4], 0, []⟩, GGTWNKill.tv ⟨5, [], 5, [3]⟩]),
    ((1, 2, 1), [GGTWNKill.tv ⟨3, [], 3, [5]⟩, GGTWNKill.line ⟨6, [5, 4], 0, []⟩, GGTWNKill.tv ⟨3,
        [], 4, [5]⟩, GGTWNKill.tv ⟨4, [], 4, [6]⟩]),
    ((1, 2, 0), [GGTWNKill.tv ⟨6, [], 6, [4]⟩, GGTWNKill.tv ⟨3, [], 3, [5]⟩, GGTWNKill.tv ⟨5, [],
        6, [3, 4]⟩])],
  [
    ((0, 1, 1, 1), [(([0, 1, 2, 0, 1], [2, 0, 0, 1, 2]), GGTWLReason.hk ⟨0, [4, 5, 1], 1, []⟩),
        (([0, 1, 2, 0, 2], [2, 0, 0, 1, 1]), GGTWLReason.hk ⟨0, [4, 5, 1], 1, []⟩)]),
    ((0, 1, 1, 2), [(([0, 2, 1, 0, 1], [2, 0, 0, 1, 2]), GGTWLReason.hk ⟨5, [4, 0, 1], 3, []⟩),
        (([0, 2, 1, 0, 2], [2, 0, 0, 1, 1]), GGTWLReason.hk ⟨5, [4, 0, 1], 3, []⟩), (([1, 1, 1, 1,
        1], [2, 0, 0, 2, 1]), GGTWLReason.hk ⟨5, [4, 0], 3, []⟩), (([1, 1, 1, 1, 2], [2, 0, 0, 2,
        2]), GGTWLReason.hk ⟨5, [4, 0], 3, []⟩), (([2, 0, 1, 2, 1], [2, 0, 0, 0, 1]),
        GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([2, 0, 1, 2, 2], [2, 0, 0, 0, 2]),
        GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩)]),
    ((0, 1, 2, 1), [(([0, 1, 2, 0, 1], [1, 0, 0, 2, 2]), GGTWLReason.hk ⟨5, [4, 0, 1], 3, []⟩),
        (([0, 1, 2, 0, 2], [1, 0, 0, 2, 1]), GGTWLReason.hk ⟨5, [4, 0, 1], 3, []⟩), (([1, 0, 2, 1,
        1], [1, 0, 0, 0, 1]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([1, 0, 2, 1, 2], [1,
        0, 0, 0, 2]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([2, 2, 2, 2, 1], [1, 0, 0, 1,
        1]), GGTWLReason.hk ⟨5, [4, 0], 3, []⟩), (([2, 2, 2, 2, 2], [1, 0, 0, 1, 2]),
        GGTWLReason.hk ⟨5, [4, 0], 3, []⟩)]),
    ((0, 2, 1, 1), [(([1, 2, 1, 0, 1], [0, 2, 0, 2, 1]), GGTWLReason.pz ⟨1, [(0, [5])], [(1, [],
        []), (2, [], []), (3, [], []), (1, [], [0])], [0, 1, 2, 3]⟩), (([1, 2, 1, 0, 2], [0, 2, 0,
        2, 2]), GGTWLReason.pz ⟨1, [(0, [4, 5])], [(1, [], []), (2, [], []), (3, [], []), (1, [],
        [0])], [0, 1, 2, 3]⟩), (([2, 1, 1, 1, 1], [0, 2, 0, 1, 2]), GGTWLReason.out6 ⟨[([1, 0, 2,
        1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([2, 2, 1, 0, 1], [2, 1, 0,
        2, 2]), ([0, 2, 1, 0, 1], [1, 0, 0, 2, 2]), ([0, 2, 1, 1, 1], [1, 0, 2, 1, 2]), ([0, 0, 1,
        0, 0], [0, 2, 2, 2, 0])], [[0], [3, 2, 3], [5, 4, 3, 1, 3, 4, 5], [5], [4, 3, 4], [4, 5,
        3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4]], [[0], [4, 3, 2, 3, 4], [4, 5, 2, 5, 4], [4, 5, 2, 1, 2,
        5, 4], [5, 2, 1, 2, 5], [3]], [(0, 5), (1, 0), (1, 2), (1, 4), (2, 1), (2, 2), (2, 4), (3,
        1), (3, 3), (3, 4), (4, 3), (5, 4), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5), (8, 3), (8,
        4), (10, 5), (12, 3), (12, 5), (13, 5), (14, 5), (15, 4), (16, 5), (17, 2), (18, 2), (19,
        5), (20, 0), (21, 2), (21, 5), (22, 0), (22, 2), (23, 2), (23, 4), (24, 0), (24, 2), (24,
        4), (25, 3), (26, 2), (26, 4), (27, 1), (27, 3), (28, 5), (29, 0), (29, 2), (30, 1), (32,
        0), (32, 4), (35, 1), (37, 1), (37, 2), (37, 4), (38, 1), (38, 3), (38, 4), (39, 3), (43,
        3), (45, 4), (49, 4), (52, 4), (53, 3), (53, 4), (54, 3), (55, 3), (55, 4), (61, 5), (62,
        3), (64, 5), (66, 2)]⟩), (([2, 1, 1, 1, 2], [0, 2, 0, 1, 1]), GGTWLReason.out6 ⟨[([1, 0,
        2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([2, 2, 1, 0, 2], [2, 1,
        0, 2, 1]), ([0, 2, 1, 0, 2], [1, 0, 0, 2, 1]), ([0, 2, 1, 1, 2], [1, 0, 2, 1, 1]), ([0, 0,
        1, 0, 0], [0, 2, 2, 2, 0])], [[0], [3, 2, 3], [5, 4, 3, 1, 3, 4, 5], [5], [4, 3, 4], [4,
        5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4]], [[0], [4, 3, 2, 3, 4], [4, 5, 2, 5, 4], [4, 5, 2, 1,
        2, 5, 4], [5, 2, 1, 2, 5], [3]], [(0, 5), (1, 0), (1, 2), (1, 4), (2, 1), (2, 2), (2, 4),
        (3, 1), (3, 3), (3, 4), (4, 3), (5, 4), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5), (8, 3),
        (8, 4), (10, 5), (12, 3), (12, 5), (13, 5), (14, 5), (15, 4), (16, 5), (17, 2), (18, 2),
        (19, 5), (20, 0), (21, 2), (21, 5), (22, 0), (22, 2), (23, 2), (23, 4), (24, 0), (24, 2),
        (24, 4), (25, 3), (26, 2), (26, 4), (27, 1), (27, 3), (28, 5), (29, 0), (29, 2), (30, 1),
        (32, 0), (32, 4), (35, 1), (37, 1), (37, 2), (37, 4), (38, 1), (38, 3), (38, 4), (39, 3),
        (43, 3), (45, 4), (49, 4), (52, 4), (53, 3), (53, 4), (54, 3), (55, 3), (55, 4), (61, 5),
        (62, 3), (64, 5), (66, 2)]⟩), (([0, 0, 1, 2, 1], [0, 2, 0, 0, 2]), GGTWLReason.out6 ⟨[([1,
        0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([1, 1, 0, 0, 0], [1,
        1, 2, 0, 0]), ([0, 0, 1, 2, 1], [0, 2, 0, 0, 2]), ([0, 0, 0, 0, 2], [0, 0, 0, 0, 1]), ([0,
        2, 2, 1, 1], [1, 2, 1, 0, 2])], [[0], [5, 4, 3, 2, 3, 4, 5], [5, 4, 3, 4, 5], [2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3,
        1], [3]], [[0], [4, 3, 2, 3, 4], [2, 1, 2], [5], [5, 2, 3, 1, 2, 5, 4, 3, 2, 1, 0, 1, 2,
        3, 4, 5, 2, 1, 3, 2, 5], [3, 1, 2, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 2, 1, 3]], [(0, 5),
        (1, 2), (2, 1), (2, 3), (3, 0), (3, 3), (4, 4), (5, 3), (6, 2), (6, 4), (8, 2), (8, 4),
        (9, 4), (9, 5), (11, 1), (11, 4), (11, 5), (13, 3), (13, 5), (15, 4), (15, 5), (16, 3),
        (16, 5), (18, 5), (20, 3), (20, 5), (21, 2), (22, 5), (24, 2), (25, 2), (25, 5), (26, 2),
        (27, 3), (28, 2), (29, 1), (30, 5), (31, 2), (32, 3), (33, 4), (34, 1), (35, 0), (36, 2),
        (37, 1), (37, 3), (38, 4), (40, 0), (42, 1), (42, 3), (43, 0), (43, 3), (44, 4), (47, 0),
        (47, 3), (48, 4), (49, 3), (50, 4), (52, 3), (53, 2), (53, 4), (55, 4), (57, 2), (57, 4),
        (58, 4), (61, 1), (61, 4), (63, 3), (64, 4), (65, 3), (67, 3), (69, 2), (70, 5)]⟩), (([0,
        0, 1, 2, 2], [0, 2, 0, 0, 1]), GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0,
        1, 1, 1, 0], [2, 1, 0, 1, 0]), ([1, 1, 0, 0, 0], [1, 1, 2, 0, 0]), ([0, 0, 1, 2, 2], [0,
        2, 0, 0, 1]), ([0, 0, 0, 0, 1], [0, 0, 0, 0, 2]), ([0, 2, 2, 1, 2], [1, 2, 1, 0, 1])],
        [[0], [5, 4, 3, 2, 3, 4, 5], [5, 4, 3, 4, 5], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2], [1,
        3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [3]], [[0], [4, 3, 2, 3, 4],
        [2, 1, 2], [5], [5, 2, 3, 1, 2, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 2, 1, 3, 2, 5], [3, 1, 2,
        5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 2, 1, 3]], [(0, 5), (1, 2), (2, 1), (2, 3), (3, 0), (3,
        3), (4, 4), (5, 3), (6, 2), (6, 4), (8, 2), (8, 4), (9, 4), (9, 5), (11, 1), (11, 4), (11,
        5), (13, 3), (13, 5), (15, 4), (15, 5), (16, 3), (16, 5), (18, 5), (20, 3), (20, 5), (21,
        2), (22, 5), (24, 2), (25, 2), (25, 5), (26, 2), (27, 3), (28, 2), (29, 1), (30, 5), (31,
        2), (32, 3), (33, 4), (34, 1), (35, 0), (36, 2), (37, 1), (37, 3), (38, 4), (40, 0), (42,
        1), (42, 3), (43, 0), (43, 3), (44, 4), (47, 0), (47, 3), (48, 4), (49, 3), (50, 4), (52,
        3), (53, 2), (53, 4), (55, 4), (57, 2), (57, 4), (58, 4), (61, 1), (61, 4), (63, 3), (64,
        4), (65, 3), (67, 3), (69, 2), (70, 5)]⟩)]),
    ((0, 3, 1, 1), [(([2, 1, 0, 0, 1], [0, 0, 2, 0, 2]), GGTWLReason.hk ⟨0, [4, 3, 5], 0, []⟩),
        (([2, 1, 0, 0, 2], [0, 0, 2, 0, 1]), GGTWLReason.hk ⟨0, [4, 3, 5], 0, []⟩)]),
    ((0, 3, 1, 2), [(([1, 2, 0, 0, 1], [0, 0, 2, 0, 2]), GGTWLReason.hk ⟨5, [4, 3, 0], 3, []⟩),
        (([1, 2, 0, 0, 2], [0, 0, 2, 0, 1]), GGTWLReason.hk ⟨5, [4, 3, 0], 3, []⟩), (([2, 1, 0, 1,
        1], [0, 0, 2, 1, 1]), GGTWLReason.hk ⟨5, [4, 0], 3, []⟩), (([2, 1, 0, 1, 2], [0, 0, 2, 1,
        2]), GGTWLReason.hk ⟨5, [4, 0], 3, []⟩), (([0, 0, 0, 2, 1], [0, 0, 2, 2, 1]),
        GGTWLReason.hk ⟨5, [4, 0, 1, 2, 3], 3, []⟩), (([0, 0, 0, 2, 2], [0, 0, 2, 2, 2]),
        GGTWLReason.hk ⟨5, [4, 0, 1, 2, 3], 3, []⟩)]),
    ((0, 3, 2, 1), [(([2, 1, 0, 0, 1], [0, 0, 1, 0, 2]), GGTWLReason.hk ⟨5, [4, 3, 0], 3, []⟩),
        (([2, 1, 0, 0, 2], [0, 0, 1, 0, 1]), GGTWLReason.hk ⟨5, [4, 3, 0], 3, []⟩), (([0, 0, 0, 1,
        1], [0, 0, 1, 1, 1]), GGTWLReason.hk ⟨5, [4, 0, 1, 2, 3], 3, []⟩), (([0, 0, 0, 1, 2], [0,
        0, 1, 1, 2]), GGTWLReason.hk ⟨5, [4, 0, 1, 2, 3], 3, []⟩), (([1, 2, 0, 2, 1], [0, 0, 1, 2,
        1]), GGTWLReason.hk ⟨5, [4, 0], 3, []⟩), (([1, 2, 0, 2, 2], [0, 0, 1, 2, 2]),
        GGTWLReason.hk ⟨5, [4, 0], 3, []⟩)]),
    ((1, 0, 1, 1), [(([1, 2, 0, 0, 1], [0, 0, 1, 0, 2]), GGTWLReason.hk ⟨2, [3, 5, 4, 3], 0, []⟩),
        (([1, 2, 0, 0, 2], [0, 0, 1, 0, 1]), GGTWLReason.hk ⟨2, [3, 5, 4, 3], 0, []⟩)]),
    ((1, 0, 1, 2), [(([2, 1, 0, 0, 1], [0, 0, 1, 0, 2]), GGTWLReason.hk ⟨5, [3, 4, 2, 3], 3, []⟩),
        (([2, 1, 0, 0, 2], [0, 0, 1, 0, 1]), GGTWLReason.hk ⟨5, [3, 4, 2, 3], 3, []⟩), (([2, 1, 0,
        1, 1], [0, 0, 2, 1, 1]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([2, 1, 0, 1, 2],
        [0, 0, 2, 1, 2]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([2, 1, 0, 2, 1], [0, 0,
        0, 2, 1]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([2, 1, 0, 2, 2], [0, 0, 0, 2,
        2]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩)]),
    ((1, 0, 2, 1), [(([1, 2, 0, 0, 1], [0, 0, 2, 0, 2]), GGTWLReason.hk ⟨5, [3, 4, 2, 3], 3, []⟩),
        (([1, 2, 0, 0, 2], [0, 0, 2, 0, 1]), GGTWLReason.hk ⟨5, [3, 4, 2, 3], 3, []⟩), (([1, 2, 0,
        1, 1], [0, 0, 0, 1, 1]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([1, 2, 0, 1, 2],
        [0, 0, 0, 1, 2]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([1, 2, 0, 2, 1], [0, 0,
        1, 2, 1]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩), (([1, 2, 0, 2, 2], [0, 0, 1, 2,
        2]), GGTWLReason.hk ⟨5, [4, 3, 2, 1, 0], 3, []⟩)]),
    ((1, 1, 1, 1), [(([0, 1, 2, 0, 1], [2, 0, 0, 1, 2]), GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2,
        0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([2, 1, 0, 1, 0], [0, 0, 1, 2, 0]), ([0,
        2, 1, 0, 1], [1, 0, 0, 2, 2]), ([0, 0, 0, 0, 2], [0, 0, 0, 0, 1]), ([0, 2, 1, 1, 2], [1,
        0, 2, 1, 1])], [[0], [5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0,
        2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2], [5, 4, 3, 4, 5],
        [4, 3, 4]], [[0], [4, 3, 2, 3, 4], [3, 2, 1, 0, 1, 2, 3], [4, 1, 5, 2, 1, 0, 1, 2, 5, 1,
        4], [5, 4, 1, 5, 2, 1, 0, 1, 2, 5, 1, 4, 5], [5, 4, 5]], [(0, 5), (1, 1), (1, 4), (2, 0),
        (2, 2), (2, 4), (3, 3), (4, 2), (4, 4), (5, 3), (5, 4), (6, 3), (6, 5), (7, 2), (8, 1),
        (8, 3), (8, 4), (9, 3), (9, 5), (11, 5), (12, 5), (15, 3), (15, 4), (15, 5), (17, 5), (18,
        5), (19, 1), (20, 1), (21, 4), (22, 2), (22, 5), (23, 5), (24, 4), (25, 1), (26, 1), (26,
        4), (27, 2), (28, 0), (30, 5), (31, 4), (32, 1), (32, 4), (33, 3), (34, 0), (34, 2), (35,
        2), (35, 4), (37, 3), (39, 1), (41, 0), (41, 2), (41, 4), (42, 3), (44, 2), (45, 3), (47,
        5), (49, 0), (50, 2), (50, 4), (51, 3), (51, 4), (52, 3), (54, 3), (58, 1), (58, 3), (58,
        4), (59, 3), (64, 3), (64, 4), (68, 2), (69, 5)]⟩), (([0, 1, 2, 0, 2], [2, 0, 0, 1, 1]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]),
        ([2, 1, 0, 1, 0], [0, 0, 1, 2, 0]), ([0, 2, 1, 0, 2], [1, 0, 0, 2, 1]), ([0, 0, 0, 0, 1],
        [0, 0, 0, 0, 2]), ([0, 2, 1, 1, 1], [1, 0, 2, 1, 2])], [[0], [5, 4, 1, 3, 2, 0, 2, 3, 1,
        4, 5], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [2, 3, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 3, 2], [5, 4, 3, 4, 5], [4, 3, 4]], [[0], [4, 3, 2, 3, 4], [3, 2, 1, 0, 1,
        2, 3], [4, 1, 5, 2, 1, 0, 1, 2, 5, 1, 4], [5, 4, 1, 5, 2, 1, 0, 1, 2, 5, 1, 4, 5], [5, 4,
        5]], [(0, 5), (1, 1), (1, 4), (2, 0), (2, 2), (2, 4), (3, 3), (4, 2), (4, 4), (5, 3), (5,
        4), (6, 3), (6, 5), (7, 2), (8, 1), (8, 3), (8, 4), (9, 3), (9, 5), (11, 5), (12, 5), (15,
        3), (15, 4), (15, 5), (17, 5), (18, 5), (19, 1), (20, 1), (21, 4), (22, 2), (22, 5), (23,
        5), (24, 4), (25, 1), (26, 1), (26, 4), (27, 2), (28, 0), (30, 5), (31, 4), (32, 1), (32,
        4), (33, 3), (34, 0), (34, 2), (35, 2), (35, 4), (37, 3), (39, 1), (41, 0), (41, 2), (41,
        4), (42, 3), (44, 2), (45, 3), (47, 5), (49, 0), (50, 2), (50, 4), (51, 3), (51, 4), (52,
        3), (54, 3), (58, 1), (58, 3), (58, 4), (59, 3), (64, 3), (64, 4), (68, 2), (69, 5)]⟩),
        (([0, 1, 2, 1, 1], [2, 0, 2, 0, 1]), GGTWLReason.pz ⟨1, [(1, [3, 5])], [(0, [], []), (1,
        [], []), (2, [], []), (0, [], [0])], [0, 1, 2, 3]⟩), (([0, 1, 2, 1, 2], [2, 0, 2, 0, 2]),
        GGTWLReason.pz ⟨1, [(1, [5, 3, 2])], [(0, [], []), (1, [], []), (2, [], []), (0, [],
        [0])], [0, 1, 2, 3]⟩), (([0, 1, 2, 2, 1], [2, 0, 1, 2, 2]), GGTWLReason.out6 ⟨[([1, 0, 2,
        1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([2, 1, 0, 1, 0], [0, 0, 1,
        2, 0]), ([0, 0, 2, 1, 1], [0, 1, 0, 0, 2]), ([0, 2, 1, 1, 1], [1, 0, 2, 1, 2]), ([0, 1, 2,
        2, 1], [2, 0, 1, 2, 2])], [[0], [4, 3, 2, 0, 2, 3, 4], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2,
        3, 1, 4, 3, 2, 5, 4, 3], [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5], [4, 3, 1, 3, 4],
        [5]], [[0], [4, 3, 2, 3, 4], [3, 2, 1, 0, 1, 2, 3], [2, 1, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4,
        5, 1, 2], [4, 1, 5, 2, 1, 0, 1, 2, 5, 1, 4], [5]], [(0, 5), (1, 1), (1, 3), (1, 4), (2,
        0), (2, 2), (2, 3), (2, 4), (3, 2), (5, 2), (5, 3), (5, 4), (6, 4), (7, 5), (8, 5), (10,
        1), (10, 4), (11, 5), (12, 5), (13, 3), (13, 5), (14, 4), (16, 4), (16, 5), (17, 3), (17,
        5), (18, 1), (18, 4), (19, 1), (21, 1), (23, 3), (23, 5), (24, 3), (24, 4), (26, 1), (27,
        4), (29, 2), (30, 0), (31, 2), (31, 5), (32, 1), (32, 3), (32, 4), (33, 4), (34, 3), (35,
        0), (35, 2), (36, 5), (37, 3), (41, 0), (41, 2), (41, 3), (41, 4), (45, 2), (46, 2), (47,
        3), (50, 2), (50, 3), (50, 4), (51, 4), (54, 1), (55, 3), (57, 1), (57, 4), (60, 3), (61,
        0), (63, 4), (64, 3), (67, 3), (67, 5), (69, 2)]⟩), (([0, 1, 2, 2, 2], [2, 0, 1, 2, 1]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]),
        ([2, 1, 0, 1, 0], [0, 0, 1, 2, 0]), ([0, 0, 2, 1, 2], [0, 1, 0, 0, 1]), ([0, 2, 1, 1, 2],
        [1, 0, 2, 1, 1]), ([0, 1, 2, 2, 2], [2, 0, 1, 2, 1])], [[0], [4, 3, 2, 0, 2, 3, 4], [3, 4,
        5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3], [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4,
        3, 2, 5], [4, 3, 1, 3, 4], [5]], [[0], [4, 3, 2, 3, 4], [3, 2, 1, 0, 1, 2, 3], [2, 1, 5,
        4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 1, 2], [4, 1, 5, 2, 1, 0, 1, 2, 5, 1, 4], [5]], [(0, 5), (1,
        1), (1, 3), (1, 4), (2, 0), (2, 2), (2, 3), (2, 4), (3, 2), (5, 2), (5, 3), (5, 4), (6,
        4), (7, 5), (8, 5), (10, 1), (10, 4), (11, 5), (12, 5), (13, 3), (13, 5), (14, 4), (16,
        4), (16, 5), (17, 3), (17, 5), (18, 1), (18, 4), (19, 1), (21, 1), (23, 3), (23, 5), (24,
        3), (24, 4), (26, 1), (27, 4), (29, 2), (30, 0), (31, 2), (31, 5), (32, 1), (32, 3), (32,
        4), (33, 4), (34, 3), (35, 0), (35, 2), (36, 5), (37, 3), (41, 0), (41, 2), (41, 3), (41,
        4), (45, 2), (46, 2), (47, 3), (50, 2), (50, 3), (50, 4), (51, 4), (54, 1), (55, 3), (57,
        1), (57, 4), (60, 3), (61, 0), (63, 4), (64, 3), (67, 3), (67, 5), (69, 2)]⟩)]),
    ((1, 2, 1, 1), [(([0, 0, 1, 2, 1], [0, 2, 0, 0, 2]), GGTWLReason.hk ⟨1, [3, 2, 5, 4, 3, 2], 0,
        []⟩), (([0, 0, 1, 2, 2], [0, 2, 0, 0, 1]), GGTWLReason.hk ⟨1, [3, 2, 5, 4, 3, 2], 0, []⟩)]),
    ((1, 2, 1, 2), [(([0, 0, 2, 0, 1], [0, 2, 2, 2, 1]), GGTWLReason.hk ⟨5, [4, 3], 3, []⟩), (([0,
        0, 2, 0, 2], [0, 2, 2, 2, 2]), GGTWLReason.hk ⟨5, [4, 3], 3, []⟩), (([0, 0, 2, 1, 1], [0,
        2, 0, 0, 2]), GGTWLReason.hk ⟨5, [3, 4, 2, 3, 1, 2], 3, []⟩), (([0, 0, 2, 1, 2], [0, 2, 0,
        0, 1]), GGTWLReason.hk ⟨5, [3, 4, 2, 3, 1, 2], 3, []⟩), (([0, 0, 2, 2, 1], [0, 2, 1, 1,
        1]), GGTWLReason.hk ⟨5, [4, 3], 3, []⟩), (([0, 0, 2, 2, 2], [0, 2, 1, 1, 2]),
        GGTWLReason.hk ⟨5, [4, 3], 3, []⟩)]),
    ((1, 2, 2, 1), [(([0, 0, 1, 0, 1], [0, 1, 1, 1, 1]), GGTWLReason.hk ⟨5, [4, 3], 3, []⟩), (([0,
        0, 1, 0, 2], [0, 1, 1, 1, 2]), GGTWLReason.hk ⟨5, [4, 3], 3, []⟩), (([0, 0, 1, 1, 1], [0,
        1, 2, 2, 1]), GGTWLReason.hk ⟨5, [4, 3], 3, []⟩), (([0, 0, 1, 1, 2], [0, 1, 2, 2, 2]),
        GGTWLReason.hk ⟨5, [4, 3], 3, []⟩), (([0, 0, 1, 2, 1], [0, 1, 0, 0, 2]),
        GGTWLReason.hk ⟨5, [3, 4, 2, 3, 1, 2], 3, []⟩), (([0, 0, 1, 2, 2], [0, 1, 0, 0, 1]),
        GGTWLReason.hk ⟨5, [3, 4, 2, 3, 1, 2], 3, []⟩)])],
  [
    ((0, 1, 4), [(([0, 1, 2, 0, 1], [2, 0, 0, 1, 2], [2, 1, 0, 0, 1], [0, 0, 2, 0, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 2, 1, 1, 2], [1, 0, 2, 1, 1]),
        ([1, 1, 1, 0, 0], [1, 0, 1, 2, 0]), ([0, 2, 2, 1, 2], [1, 2, 1, 0, 1]), ([0, 0, 1, 1, 0],
        [0, 2, 1, 1, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0])], [[0], [5, 4, 2, 3, 1, 3, 2, 4, 5],
        [5, 4, 5], [3, 1, 3], [4, 3, 1, 3, 4], [4, 3, 4], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        5]], [[0], [5, 4, 5], [3, 2, 1, 2, 3], [6, 1, 0, 1, 6], [4, 3, 4], [4, 3, 2, 3, 4]], [(0,
        5), (0, 6), (1, 1), (1, 4), (1, 6), (2, 0), (2, 3), (3, 0), (3, 2), (3, 4), (3, 6), (4,
        3), (4, 6), (5, 0), (5, 3), (7, 2), (8, 2), (9, 3), (9, 4), (9, 6), (10, 5), (10, 6), (11,
        3), (12, 2), (13, 0), (15, 2), (16, 1), (17, 1), (17, 3), (18, 6), (19, 5), (19, 6), (20,
        3), (21, 6), (23, 2), (26, 1), (27, 5), (28, 3), (28, 5), (29, 6), (30, 0), (30, 3), (31,
        1), (31, 6), (32, 3), (33, 2), (33, 4), (35, 1), (36, 0), (36, 5), (37, 4), (38, 2), (41,
        3), (42, 2), (42, 4), (46, 1), (46, 4), (48, 0), (48, 5), (53, 2), (54, 1), (54, 4), (56,
        0), (56, 4), (56, 5), (61, 4), (61, 5), (62, 3), (63, 4), (66, 3), (70, 2)]⟩), (([0, 1, 2,
        0, 2], [2, 0, 0, 1, 1], [2, 1, 0, 0, 2], [0, 0, 2, 0, 1]), GGTWLReason.out6 ⟨[([1, 0, 2,
        1, 0], [2, 0, 0, 0, 0]), ([0, 2, 1, 1, 1], [1, 0, 2, 1, 2]), ([1, 1, 1, 0, 0], [1, 0, 1,
        2, 0]), ([0, 2, 2, 1, 1], [1, 2, 1, 0, 2]), ([0, 0, 1, 1, 0], [0, 2, 1, 1, 0]), ([0, 1, 1,
        1, 0], [2, 1, 0, 1, 0])], [[0], [5, 4, 2, 3, 1, 3, 2, 4, 5], [5, 4, 5], [3, 1, 3], [4, 3,
        1, 3, 4], [4, 3, 4], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5]], [[0], [5, 4, 5], [3, 2, 1,
        2, 3], [6, 1, 0, 1, 6], [4, 3, 4], [4, 3, 2, 3, 4]], [(0, 5), (0, 6), (1, 1), (1, 4), (1,
        6), (2, 0), (2, 3), (3, 0), (3, 2), (3, 4), (3, 6), (4, 3), (4, 6), (5, 0), (5, 3), (7,
        2), (8, 2), (9, 3), (9, 4), (9, 6), (10, 5), (10, 6), (11, 3), (12, 2), (13, 0), (15, 2),
        (16, 1), (17, 1), (17, 3), (18, 6), (19, 5), (19, 6), (20, 3), (21, 6), (23, 2), (26, 1),
        (27, 5), (28, 3), (28, 5), (29, 6), (30, 0), (30, 3), (31, 1), (31, 6), (32, 3), (33, 2),
        (33, 4), (35, 1), (36, 0), (36, 5), (37, 4), (38, 2), (41, 3), (42, 2), (42, 4), (46, 1),
        (46, 4), (48, 0), (48, 5), (53, 2), (54, 1), (54, 4), (56, 0), (56, 4), (56, 5), (61, 4),
        (61, 5), (62, 3), (63, 4), (66, 3), (70, 2)]⟩)]),
    ((0, 1, 0), [(([0, 1, 2, 0, 1], [2, 0, 0, 1, 2], [0, 0, 0, 0, 1], [0, 0, 0, 0, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 2, 2, 1, 2], [1, 2, 1, 0, 1]),
        ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 2, 1, 2], [0, 1, 0, 0, 1]), ([0, 1, 1, 0, 0],
        [2, 1, 1, 2, 0]), ([0, 0, 0, 1, 0], [0, 0, 2, 2, 0])], [[0], [1, 3, 2, 0, 2, 3, 1], [3, 1,
        3], [4, 3, 1, 3, 4], [5], [5, 4, 3, 4, 5], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        2, 5, 4, 3]], [[0], [5, 4, 3, 4, 5], [2, 1, 0, 1, 2], [5, 4, 3, 2, 3, 4, 5], [3, 2, 3],
        [4]], [(0, 5), (0, 6), (1, 1), (1, 4), (1, 6), (2, 5), (3, 0), (3, 2), (3, 4), (3, 6), (4,
        3), (4, 6), (5, 5), (6, 1), (6, 4), (7, 2), (7, 4), (7, 6), (8, 3), (8, 4), (8, 6), (9,
        3), (9, 5), (9, 6), (10, 5), (11, 2), (11, 6), (12, 5), (13, 1), (13, 4), (14, 0), (14,
        2), (14, 4), (15, 3), (16, 3), (17, 3), (17, 5), (18, 5), (19, 6), (20, 5), (21, 5), (22,
        5), (22, 6), (25, 1), (26, 6), (27, 5), (28, 4), (30, 3), (32, 3), (33, 3), (33, 5), (34,
        2), (36, 5), (37, 1), (38, 1), (39, 5), (40, 1), (41, 1), (42, 4), (45, 5), (46, 4), (47,
        3), (48, 2), (50, 5), (53, 1), (53, 4), (56, 1), (56, 4), (61, 3), (62, 2), (64, 4)]⟩),
        (([0, 1, 2, 0, 2], [2, 0, 0, 1, 1], [0, 0, 0, 0, 2], [0, 0, 0, 0, 1]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 2, 2, 1, 1], [1, 2, 1, 0, 2]),
        ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 2, 1, 1], [0, 1, 0, 0, 2]), ([0, 1, 1, 0, 0],
        [2, 1, 1, 2, 0]), ([0, 0, 0, 1, 0], [0, 0, 2, 2, 0])], [[0], [1, 3, 2, 0, 2, 3, 1], [3, 1,
        3], [4, 3, 1, 3, 4], [5], [5, 4, 3, 4, 5], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        2, 5, 4, 3]], [[0], [5, 4, 3, 4, 5], [2, 1, 0, 1, 2], [5, 4, 3, 2, 3, 4, 5], [3, 2, 3],
        [4]], [(0, 5), (0, 6), (1, 1), (1, 4), (1, 6), (2, 5), (3, 0), (3, 2), (3, 4), (3, 6), (4,
        3), (4, 6), (5, 5), (6, 1), (6, 4), (7, 2), (7, 4), (7, 6), (8, 3), (8, 4), (8, 6), (9,
        3), (9, 5), (9, 6), (10, 5), (11, 2), (11, 6), (12, 5), (13, 1), (13, 4), (14, 0), (14,
        2), (14, 4), (15, 3), (16, 3), (17, 3), (17, 5), (18, 5), (19, 6), (20, 5), (21, 5), (22,
        5), (22, 6), (25, 1), (26, 6), (27, 5), (28, 4), (30, 3), (32, 3), (33, 3), (33, 5), (34,
        2), (36, 5), (37, 1), (38, 1), (39, 5), (40, 1), (41, 1), (42, 4), (45, 5), (46, 4), (47,
        3), (48, 2), (50, 5), (53, 1), (53, 4), (56, 1), (56, 4), (61, 3), (62, 2), (64, 4)]⟩)]),
    ((0, 3, 2), [(([2, 1, 0, 0, 1], [0, 0, 2, 0, 2], [0, 1, 2, 0, 1], [2, 0, 0, 1, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 2, 1, 1, 2], [1, 0, 2, 1, 1]),
        ([1, 1, 1, 0, 0], [1, 0, 1, 2, 0]), ([0, 0, 1, 0, 0], [0, 2, 2, 2, 0]), ([0, 0, 1, 1, 0],
        [0, 2, 1, 1, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0])], [[0], [5, 4, 3, 2, 3, 4, 5], [5, 4,
        5], [3], [4, 3, 4], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5], [4, 3, 1, 3, 4]], [[0], [6,
        4, 6], [3, 2, 1, 2, 3], [3], [4, 3, 4], [4, 3, 2, 3, 4]], [(0, 5), (0, 6), (1, 0), (1, 3),
        (1, 6), (2, 1), (2, 4), (3, 1), (3, 3), (3, 6), (4, 2), (4, 4), (4, 6), (5, 1), (5, 4),
        (6, 2), (8, 2), (9, 2), (9, 5), (9, 6), (10, 4), (11, 1), (11, 4), (11, 6), (13, 1), (14,
        2), (16, 3), (18, 5), (18, 6), (19, 6), (22, 4), (22, 6), (23, 3), (24, 1), (25, 2), (26,
        3), (27, 5), (28, 3), (28, 6), (29, 1), (31, 3), (31, 6), (32, 1), (32, 4), (33, 5), (34,
        0), (34, 2), (35, 3), (36, 4), (36, 5), (37, 0), (41, 2), (43, 0), (43, 2), (43, 4), (46,
        2), (47, 3), (48, 4), (48, 5), (53, 2), (54, 3), (54, 4), (56, 3), (57, 4), (57, 5), (60,
        1), (60, 3), (61, 5), (63, 4), (66, 3), (70, 2)]⟩), (([2, 1, 0, 0, 2], [0, 0, 2, 0, 1],
        [0, 1, 2, 0, 2], [2, 0, 0, 1, 1]), GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]),
        ([0, 2, 1, 1, 1], [1, 0, 2, 1, 2]), ([1, 1, 1, 0, 0], [1, 0, 1, 2, 0]), ([0, 0, 1, 0, 0],
        [0, 2, 2, 2, 0]), ([0, 0, 1, 1, 0], [0, 2, 1, 1, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0])],
        [[0], [5, 4, 3, 2, 3, 4, 5], [5, 4, 5], [3], [4, 3, 4], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4,
        3, 5], [4, 3, 1, 3, 4]], [[0], [6, 4, 6], [3, 2, 1, 2, 3], [3], [4, 3, 4], [4, 3, 2, 3,
        4]], [(0, 5), (0, 6), (1, 0), (1, 3), (1, 6), (2, 1), (2, 4), (3, 1), (3, 3), (3, 6), (4,
        2), (4, 4), (4, 6), (5, 1), (5, 4), (6, 2), (8, 2), (9, 2), (9, 5), (9, 6), (10, 4), (11,
        1), (11, 4), (11, 6), (13, 1), (14, 2), (16, 3), (18, 5), (18, 6), (19, 6), (22, 4), (22,
        6), (23, 3), (24, 1), (25, 2), (26, 3), (27, 5), (28, 3), (28, 6), (29, 1), (31, 3), (31,
        6), (32, 1), (32, 4), (33, 5), (34, 0), (34, 2), (35, 3), (36, 4), (36, 5), (37, 0), (41,
        2), (43, 0), (43, 2), (43, 4), (46, 2), (47, 3), (48, 4), (48, 5), (53, 2), (54, 3), (54,
        4), (56, 3), (57, 4), (57, 5), (60, 1), (60, 3), (61, 5), (63, 4), (66, 3), (70, 2)]⟩)]),
    ((0, 3, 0), [(([2, 1, 0, 0, 1], [0, 0, 2, 0, 2], [0, 0, 0, 0, 1], [0, 0, 0, 0, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]),
        ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 2, 1, 1], [0, 1, 0, 0, 2]), ([0, 0, 0, 0, 1],
        [0, 0, 0, 0, 2]), ([0, 2, 2, 1, 2], [1, 2, 1, 0, 1])], [[0], [5, 4, 3, 2, 0, 2, 3, 4, 5],
        [5, 4, 3, 4, 5], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [4, 3, 2, 3, 4], [4]], [[0], [4, 3, 2, 3, 4], [2, 1, 0,
        1, 2], [6, 5, 2, 1, 0, 1, 2, 5, 6], [6], [5, 1, 0, 1, 5]], [(0, 5), (0, 6), (1, 0), (1,
        3), (1, 6), (2, 5), (3, 1), (3, 3), (3, 6), (4, 2), (4, 4), (4, 6), (5, 5), (6, 0), (6,
        3), (7, 2), (7, 3), (7, 6), (8, 2), (8, 4), (8, 5), (8, 6), (9, 5), (10, 1), (10, 4), (10,
        6), (11, 6), (12, 5), (13, 0), (13, 3), (14, 1), (14, 3), (15, 2), (15, 4), (16, 6), (17,
        4), (17, 5), (17, 6), (18, 5), (19, 5), (20, 5), (23, 0), (24, 4), (24, 6), (26, 5), (27,
        5), (28, 3), (29, 1), (31, 2), (31, 3), (32, 5), (33, 1), (35, 5), (36, 5), (37, 0), (39,
        0), (40, 3), (41, 3), (42, 1), (44, 5), (45, 3), (46, 3), (48, 2), (50, 5), (53, 0), (53,
        3), (56, 1), (59, 2), (60, 0), (60, 3), (64, 0)]⟩), (([2, 1, 0, 0, 2], [0, 0, 2, 0, 1],
        [0, 0, 0, 0, 2], [0, 0, 0, 0, 1]), GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]),
        ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 2, 1, 2],
        [0, 1, 0, 0, 1]), ([0, 0, 0, 0, 2], [0, 0, 0, 0, 1]), ([0, 2, 2, 1, 1], [1, 2, 1, 0, 2])],
        [[0], [5, 4, 3, 2, 0, 2, 3, 4, 5], [5, 4, 3, 4, 5], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        2], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [4, 3, 2, 3, 4],
        [4]], [[0], [4, 3, 2, 3, 4], [2, 1, 0, 1, 2], [6, 5, 2, 1, 0, 1, 2, 5, 6], [6], [5, 1, 0,
        1, 5]], [(0, 5), (0, 6), (1, 0), (1, 3), (1, 6), (2, 5), (3, 1), (3, 3), (3, 6), (4, 2),
        (4, 4), (4, 6), (5, 5), (6, 0), (6, 3), (7, 2), (7, 3), (7, 6), (8, 2), (8, 4), (8, 5),
        (8, 6), (9, 5), (10, 1), (10, 4), (10, 6), (11, 6), (12, 5), (13, 0), (13, 3), (14, 1),
        (14, 3), (15, 2), (15, 4), (16, 6), (17, 4), (17, 5), (17, 6), (18, 5), (19, 5), (20, 5),
        (23, 0), (24, 4), (24, 6), (26, 5), (27, 5), (28, 3), (29, 1), (31, 2), (31, 3), (32, 5),
        (33, 1), (35, 5), (36, 5), (37, 0), (39, 0), (40, 3), (41, 3), (42, 1), (44, 5), (45, 3),
        (46, 3), (48, 2), (50, 5), (53, 0), (53, 3), (56, 1), (59, 2), (60, 0), (60, 3), (64,
        0)]⟩)]),
    ((1, 0, 3), [(([1, 2, 0, 0, 1], [0, 0, 1, 0, 2], [0, 0, 1, 2, 1], [0, 2, 0, 0, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]),
        ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 2, 1, 0, 2], [1, 0, 0, 2, 1]), ([0, 1, 1, 2, 1],
        [2, 1, 2, 0, 2]), ([0, 2, 2, 1, 1], [1, 2, 1, 0, 2])], [[0], [4, 1, 3, 2, 0, 2, 3, 1, 4],
        [4, 3, 1, 3, 4], [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5], [3, 4, 5, 2, 3, 4, 1, 3,
        2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3], [5, 4, 2, 3, 1, 3, 2, 4, 5], [3, 1, 3]], [[0], [4, 3, 2,
        3, 4], [2, 1, 0, 1, 2], [5, 3, 2, 1, 2, 3, 5], [6, 2, 6], [5, 1, 0, 1, 5]], [(0, 5), (0,
        6), (1, 0), (1, 3), (1, 6), (2, 2), (3, 1), (3, 3), (3, 6), (4, 2), (4, 4), (4, 6), (5,
        2), (6, 1), (6, 3), (7, 2), (7, 3), (7, 6), (8, 2), (8, 4), (8, 5), (8, 6), (9, 2), (10,
        1), (10, 4), (11, 6), (13, 1), (14, 0), (16, 6), (17, 4), (17, 5), (17, 6), (18, 2), (19,
        4), (19, 5), (20, 5), (20, 6), (21, 6), (23, 1), (27, 0), (28, 5), (29, 2), (30, 5), (30,
        6), (31, 0), (31, 6), (32, 2), (33, 1), (34, 5), (35, 3), (36, 6), (39, 0), (40, 5), (41,
        3), (42, 1), (43, 0), (43, 6), (44, 2), (45, 6), (48, 0), (50, 4), (52, 5), (53, 3), (54,
        4), (55, 0), (56, 6), (60, 5), (62, 3), (63, 4), (65, 5), (68, 4)]⟩), (([1, 2, 0, 0, 2],
        [0, 0, 1, 0, 1], [0, 0, 1, 2, 2], [0, 2, 0, 0, 1]), GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0],
        [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]),
        ([0, 2, 1, 0, 1], [1, 0, 0, 2, 2]), ([0, 1, 1, 2, 2], [2, 1, 2, 0, 1]), ([0, 2, 2, 1, 2],
        [1, 2, 1, 0, 1])], [[0], [4, 1, 3, 2, 0, 2, 3, 1, 4], [4, 3, 1, 3, 4], [5, 2, 3, 4, 1, 3,
        2, 0, 2, 3, 1, 4, 3, 2, 5], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3], [5,
        4, 2, 3, 1, 3, 2, 4, 5], [3, 1, 3]], [[0], [4, 3, 2, 3, 4], [2, 1, 0, 1, 2], [5, 3, 2, 1,
        2, 3, 5], [6, 2, 6], [5, 1, 0, 1, 5]], [(0, 5), (0, 6), (1, 0), (1, 3), (1, 6), (2, 2),
        (3, 1), (3, 3), (3, 6), (4, 2), (4, 4), (4, 6), (5, 2), (6, 1), (6, 3), (7, 2), (7, 3),
        (7, 6), (8, 2), (8, 4), (8, 5), (8, 6), (9, 2), (10, 1), (10, 4), (11, 6), (13, 1), (14,
        0), (16, 6), (17, 4), (17, 5), (17, 6), (18, 2), (19, 4), (19, 5), (20, 5), (20, 6), (21,
        6), (23, 1), (27, 0), (28, 5), (29, 2), (30, 5), (30, 6), (31, 0), (31, 6), (32, 2), (33,
        1), (34, 5), (35, 3), (36, 6), (39, 0), (40, 5), (41, 3), (42, 1), (43, 0), (43, 6), (44,
        2), (45, 6), (48, 0), (50, 4), (52, 5), (53, 3), (54, 4), (55, 0), (56, 6), (60, 5), (62,
        3), (63, 4), (65, 5), (68, 4)]⟩)]),
    ((1, 0, 0), [(([1, 2, 0, 0, 1], [0, 0, 1, 0, 2], [0, 0, 0, 0, 1], [0, 0, 0, 0, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]),
        ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 2, 1, 2], [0, 1, 0, 0, 1]), ([0, 0, 0, 0, 1],
        [0, 0, 0, 0, 2]), ([0, 2, 2, 1, 1], [1, 2, 1, 0, 2])], [[0], [5, 4, 3, 2, 0, 2, 3, 4, 5],
        [5, 4, 3, 4, 5], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [4, 3, 2, 3, 4], [4]], [[0], [4, 3, 2, 3, 4], [2, 1, 0,
        1, 2], [6, 5, 2, 1, 0, 1, 2, 5, 6], [6], [5, 1, 0, 1, 5]], [(0, 5), (0, 6), (1, 0), (1,
        3), (1, 6), (2, 5), (3, 1), (3, 3), (3, 6), (4, 2), (4, 4), (4, 6), (5, 5), (6, 0), (6,
        3), (7, 2), (7, 3), (7, 6), (8, 2), (8, 4), (8, 5), (8, 6), (9, 5), (10, 1), (10, 4), (10,
        6), (11, 6), (12, 5), (13, 0), (13, 3), (14, 1), (14, 3), (15, 2), (15, 4), (16, 6), (17,
        4), (17, 5), (17, 6), (18, 5), (19, 5), (20, 5), (23, 0), (24, 4), (24, 6), (26, 5), (27,
        5), (28, 3), (29, 1), (31, 2), (31, 3), (32, 5), (33, 1), (35, 5), (36, 5), (37, 0), (39,
        0), (40, 3), (41, 3), (42, 1), (44, 5), (45, 3), (46, 3), (48, 2), (50, 5), (53, 0), (53,
        3), (56, 1), (59, 2), (60, 0), (60, 3), (64, 0)]⟩), (([1, 2, 0, 0, 2], [0, 0, 1, 0, 1],
        [0, 0, 0, 0, 2], [0, 0, 0, 0, 1]), GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]),
        ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]), ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 2, 1, 1],
        [0, 1, 0, 0, 2]), ([0, 0, 0, 0, 2], [0, 0, 0, 0, 1]), ([0, 2, 2, 1, 2], [1, 2, 1, 0, 1])],
        [[0], [5, 4, 3, 2, 0, 2, 3, 4, 5], [5, 4, 3, 4, 5], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        2], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [4, 3, 2, 3, 4],
        [4]], [[0], [4, 3, 2, 3, 4], [2, 1, 0, 1, 2], [6, 5, 2, 1, 0, 1, 2, 5, 6], [6], [5, 1, 0,
        1, 5]], [(0, 5), (0, 6), (1, 0), (1, 3), (1, 6), (2, 5), (3, 1), (3, 3), (3, 6), (4, 2),
        (4, 4), (4, 6), (5, 5), (6, 0), (6, 3), (7, 2), (7, 3), (7, 6), (8, 2), (8, 4), (8, 5),
        (8, 6), (9, 5), (10, 1), (10, 4), (10, 6), (11, 6), (12, 5), (13, 0), (13, 3), (14, 1),
        (14, 3), (15, 2), (15, 4), (16, 6), (17, 4), (17, 5), (17, 6), (18, 5), (19, 5), (20, 5),
        (23, 0), (24, 4), (24, 6), (26, 5), (27, 5), (28, 3), (29, 1), (31, 2), (31, 3), (32, 5),
        (33, 1), (35, 5), (36, 5), (37, 0), (39, 0), (40, 3), (41, 3), (42, 1), (44, 5), (45, 3),
        (46, 3), (48, 2), (50, 5), (53, 0), (53, 3), (56, 1), (59, 2), (60, 0), (60, 3), (64,
        0)]⟩)]),
    ((1, 2, 1), [(([0, 0, 1, 2, 1], [0, 2, 0, 0, 2], [1, 2, 0, 0, 1], [0, 0, 1, 0, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2, 1, 0, 1, 0]),
        ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 1, 2, 1], [0, 2, 0, 0, 2]), ([0, 1, 1, 2, 1],
        [2, 1, 2, 0, 2]), ([0, 2, 2, 1, 1], [1, 2, 1, 0, 2])], [[0], [4, 3, 2, 0, 2, 3, 4], [4, 3,
        4], [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3,
        1, 4, 3, 2, 5, 4, 3, 1], [3], [5, 4, 3, 2, 3, 4, 5]], [[0], [4, 3, 2, 3, 4], [2, 1, 0, 1,
        2], [5], [5, 2, 5], [6, 1, 0, 1, 6]], [(0, 5), (0, 6), (1, 2), (1, 6), (2, 0), (2, 3), (3,
        1), (3, 3), (3, 6), (4, 0), (4, 3), (5, 1), (5, 3), (6, 2), (6, 4), (7, 0), (7, 3), (7,
        6), (8, 4), (9, 0), (10, 1), (10, 3), (11, 4), (12, 2), (12, 3), (13, 2), (13, 4), (13,
        6), (16, 3), (16, 6), (18, 0), (20, 1), (21, 2), (21, 3), (22, 4), (22, 6), (24, 5), (25,
        4), (25, 6), (26, 6), (27, 6), (29, 6), (30, 0), (30, 3), (31, 1), (32, 2), (33, 5), (34,
        2), (34, 4), (34, 6), (35, 6), (38, 6), (39, 0), (40, 3), (43, 1), (43, 3), (44, 4), (45,
        2), (46, 5), (48, 4), (49, 6), (50, 0), (52, 0), (54, 4), (55, 2), (55, 3), (56, 4), (58,
        5), (61, 0), (65, 5), (66, 4)]⟩), (([0, 0, 1, 2, 2], [0, 2, 0, 0, 1], [1, 2, 0, 0, 2], [0,
        0, 1, 0, 1]), GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 1, 1, 0], [2,
        1, 0, 1, 0]), ([2, 1, 2, 1, 0], [0, 1, 2, 0, 0]), ([0, 0, 1, 2, 2], [0, 2, 0, 0, 1]), ([0,
        1, 1, 2, 2], [2, 1, 2, 0, 1]), ([0, 2, 2, 1, 2], [1, 2, 1, 0, 1])], [[0], [4, 3, 2, 0, 2,
        3, 4], [4, 3, 4], [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5], [1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], [3], [5, 4, 3, 2, 3, 4, 5]], [[0], [4, 3, 2, 3,
        4], [2, 1, 0, 1, 2], [5], [5, 2, 5], [6, 1, 0, 1, 6]], [(0, 5), (0, 6), (1, 2), (1, 6),
        (2, 0), (2, 3), (3, 1), (3, 3), (3, 6), (4, 0), (4, 3), (5, 1), (5, 3), (6, 2), (6, 4),
        (7, 0), (7, 3), (7, 6), (8, 4), (9, 0), (10, 1), (10, 3), (11, 4), (12, 2), (12, 3), (13,
        2), (13, 4), (13, 6), (16, 3), (16, 6), (18, 0), (20, 1), (21, 2), (21, 3), (22, 4), (22,
        6), (24, 5), (25, 4), (25, 6), (26, 6), (27, 6), (29, 6), (30, 0), (30, 3), (31, 1), (32,
        2), (33, 5), (34, 2), (34, 4), (34, 6), (35, 6), (38, 6), (39, 0), (40, 3), (43, 1), (43,
        3), (44, 4), (45, 2), (46, 5), (48, 4), (49, 6), (50, 0), (52, 0), (54, 4), (55, 2), (55,
        3), (56, 4), (58, 5), (61, 0), (65, 5), (66, 4)]⟩)]),
    ((1, 2, 0), [(([0, 0, 1, 2, 1], [0, 2, 0, 0, 2], [0, 0, 0, 0, 1], [0, 0, 0, 0, 2]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 2, 2, 1], [2, 0, 1, 2, 2]),
        ([2, 1, 0, 1, 0], [0, 0, 1, 2, 0]), ([0, 0, 1, 2, 1], [0, 2, 0, 0, 2]), ([0, 1, 1, 1, 0],
        [2, 1, 0, 1, 0]), ([0, 0, 1, 1, 0], [0, 2, 1, 1, 0])], [[0], [1, 3, 2, 0, 2, 3, 1], [5, 4,
        5], [5, 4, 3, 1, 3, 4, 5], [4, 3, 1, 3, 4], [3], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1,
        4, 3, 2, 5, 4, 3]], [[0], [5, 3, 2, 3, 5], [3, 2, 1, 0, 1, 2, 3], [5], [4, 3, 2, 3, 4],
        [4, 3, 4]], [(0, 5), (0, 6), (1, 2), (1, 6), (2, 5), (3, 1), (3, 3), (3, 6), (4, 5), (5,
        2), (6, 0), (6, 3), (6, 6), (7, 4), (7, 6), (8, 5), (9, 2), (10, 1), (10, 3), (11, 3),
        (11, 6), (12, 2), (12, 4), (12, 6), (13, 5), (14, 6), (15, 5), (16, 2), (17, 1), (17, 3),
        (18, 0), (18, 3), (19, 4), (20, 2), (20, 4), (20, 6), (21, 5), (22, 4), (22, 5), (22, 6),
        (23, 6), (24, 5), (25, 2), (26, 5), (27, 2), (28, 1), (28, 3), (29, 0), (29, 3), (30, 4),
        (31, 3), (32, 2), (32, 4), (34, 5), (36, 5), (37, 2), (38, 5), (41, 5), (43, 1), (44, 2),
        (45, 3), (46, 0), (46, 3), (47, 4), (52, 5), (56, 1), (59, 0), (60, 3), (61, 4), (66, 0),
        (68, 4)]⟩), (([0, 0, 1, 2, 2], [0, 2, 0, 0, 1], [0, 0, 0, 0, 2], [0, 0, 0, 0, 1]),
        GGTWLReason.out6 ⟨[([1, 0, 2, 1, 0], [2, 0, 0, 0, 0]), ([0, 1, 2, 2, 2], [2, 0, 1, 2, 1]),
        ([2, 1, 0, 1, 0], [0, 0, 1, 2, 0]), ([0, 0, 1, 2, 2], [0, 2, 0, 0, 1]), ([0, 1, 1, 1, 0],
        [2, 1, 0, 1, 0]), ([0, 0, 1, 1, 0], [0, 2, 1, 1, 0])], [[0], [1, 3, 2, 0, 2, 3, 1], [5, 4,
        5], [5, 4, 3, 1, 3, 4, 5], [4, 3, 1, 3, 4], [3], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1,
        4, 3, 2, 5, 4, 3]], [[0], [5, 3, 2, 3, 5], [3, 2, 1, 0, 1, 2, 3], [5], [4, 3, 2, 3, 4],
        [4, 3, 4]], [(0, 5), (0, 6), (1, 2), (1, 6), (2, 5), (3, 1), (3, 3), (3, 6), (4, 5), (5,
        2), (6, 0), (6, 3), (6, 6), (7, 4), (7, 6), (8, 5), (9, 2), (10, 1), (10, 3), (11, 3),
        (11, 6), (12, 2), (12, 4), (12, 6), (13, 5), (14, 6), (15, 5), (16, 2), (17, 1), (17, 3),
        (18, 0), (18, 3), (19, 4), (20, 2), (20, 4), (20, 6), (21, 5), (22, 4), (22, 5), (22, 6),
        (23, 6), (24, 5), (25, 2), (26, 5), (27, 2), (28, 1), (28, 3), (29, 0), (29, 3), (30, 4),
        (31, 3), (32, 2), (32, 4), (34, 5), (36, 5), (37, 2), (38, 5), (41, 5), (43, 1), (44, 2),
        (45, 3), (46, 0), (46, 3), (47, 4), (52, 5), (56, 1), (59, 0), (60, 3), (61, 4), (66, 0),
        (68, 4)]⟩)])]⟩

@[expose] def twDataL39 (_ : Unit := ()) : GGTWLData :=
  ⟨[
    ((0, 1, 1, 1), [GGTWNKill.tv ⟨8, [], 8, [0]⟩, GGTWNKill.tv ⟨8, [], 8, [7]⟩, GGTWNKill.tv ⟨1,
        [], 2, [8, 7, 6, 5, 4, 3]⟩]),
    ((0, 1, 1, 2), [GGTWNKill.tv ⟨8, [], 8, [0]⟩, GGTWNKill.line ⟨8, [8, 7, 1], 0, []⟩,
        GGTWNKill.tv ⟨7, [], 7, [8]⟩, GGTWNKill.line ⟨8, [8, 1, 2, 0, 1], 3, []⟩]),
    ((0, 1, 2, 1), [GGTWNKill.tv ⟨8, [], 8, [0]⟩, GGTWNKill.line ⟨8, [8, 7, 1], 0, []⟩,
        GGTWNKill.line ⟨8, [8, 1, 2, 0, 1], 3, []⟩, GGTWNKill.tv ⟨7, [], 7, [8]⟩]),
    ((0, 2, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [8]⟩, GGTWNKill.line ⟨8, [8, 7, 0], 1, []⟩,
        GGTWNKill.line ⟨0, [8, 7, 2, 8, 1], 0, []⟩]),
    ((0, 3, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [8, 7, 8]⟩, GGTWNKill.line ⟨2, [8, 7, 3, 8, 6, 5, 4,
        3], 1, []⟩, GGTWNKill.line ⟨0, [8, 7, 3, 8, 2, 1], 0, []⟩]),
    ((0, 4, 1, 1), [GGTWNKill.tv ⟨7, [], 7, [8]⟩, GGTWNKill.tv ⟨8, [], 8, [0]⟩, GGTWNKill.line ⟨0,
        [8, 4, 5, 3, 4, 8, 2, 1], 0, []⟩, GGTWNKill.line ⟨0, [8, 7, 6, 5, 4, 8], 0, []⟩]),
    ((0, 5, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [8]⟩, GGTWNKill.line ⟨8, [8, 7, 0], 1, []⟩,
        GGTWNKill.line ⟨0, [8, 7, 6, 5, 8], 0, []⟩]),
    ((0, 6, 1, 1), [GGTWNKill.tv ⟨0, [], 0, [8, 7, 8]⟩, GGTWNKill.tv ⟨7, [], 8, []⟩,
        GGTWNKill.tv ⟨0, [], 1, [8, 6, 5, 4, 3, 2]⟩]),
    ((0, 6, 1, 2), [GGTWNKill.line ⟨0, [8, 7, 6, 0, 8, 1], 2, []⟩, GGTWNKill.tv ⟨0, [], 0, [8, 7,
        8]⟩, GGTWNKill.line ⟨8, [8, 6, 7, 5, 6], 4, []⟩]),
    ((0, 6, 2, 1), [GGTWNKill.line ⟨0, [8, 7, 6, 0, 8, 1], 2, []⟩, GGTWNKill.line ⟨6, [8, 7, 8],
        5, []⟩, GGTWNKill.line ⟨8, [8, 6, 7, 5, 6], 4, []⟩]),
    ((1, 0, 1, 1), [GGTWNKill.tv ⟨8, [], 8, [7]⟩, GGTWNKill.tv ⟨0, [1], 2, [8, 7, 6, 5, 4, 3]⟩,
        GGTWNKill.tv ⟨8, [], 8, [6]⟩, GGTWNKill.tv ⟨0, [], 1, [8, 6, 5, 4, 3, 2]⟩]),
    ((1, 0, 1, 2), [GGTWNKill.line ⟨8, [8, 7, 6, 0], 1, []⟩, GGTWNKill.tv ⟨8, [], 8, [7]⟩,
        GGTWNKill.tv ⟨6, [], 6, [8]⟩]),
    ((1, 0, 2, 1), [GGTWNKill.line ⟨8, [8, 7, 6, 0], 1, []⟩, GGTWNKill.tv ⟨6, [], 6, [8]⟩,
        GGTWNKill.tv ⟨8, [], 8, [7]⟩]),
    ((1, 1, 1, 1), [GGTWNKill.tv ⟨8, [], 8, [6]⟩, GGTWNKill.line ⟨0, [8, 6, 7, 5, 6, 1, 8, 2, 1],
        1, []⟩]),
    ((1, 2, 1, 1), [GGTWNKill.line ⟨2, [8, 7, 6, 8], 1, []⟩, GGTWNKill.tv ⟨8, [], 8, [6]⟩]),
    ((1, 3, 1, 1), [GGTWNKill.tv ⟨8, [], 8, [7]⟩, GGTWNKill.line ⟨2, [8, 7, 3, 8, 6, 5, 4, 3], 1,
        []⟩, GGTWNKill.tv ⟨8, [], 8, [6]⟩]),
    ((1, 4, 1, 1), [GGTWNKill.tv ⟨8, [], 8, [6]⟩, GGTWNKill.line ⟨4, [8, 6, 7, 5, 6, 8], 3, []⟩,
        GGTWNKill.tv ⟨7, [], 7, [8]⟩]),
    ((1, 5, 1, 1), [GGTWNKill.tv ⟨6, [], 6, [8]⟩, GGTWNKill.tv ⟨5, [], 5, [6, 8, 6]⟩,
        GGTWNKill.tv ⟨6, [], 7, [8]⟩]),
    ((1, 5, 1, 2), [GGTWNKill.tv ⟨6, [], 6, [8]⟩, GGTWNKill.line ⟨8, [8, 7, 5], 4, []⟩,
        GGTWNKill.line ⟨8, [8, 5, 6, 4, 5], 3, []⟩, GGTWNKill.tv ⟨6, [], 7, [8]⟩]),
    ((1, 5, 2, 1), [GGTWNKill.tv ⟨6, [], 6, [8]⟩, GGTWNKill.line ⟨8, [8, 7, 5], 4, []⟩,
        GGTWNKill.tv ⟨6, [], 7, [8]⟩, GGTWNKill.line ⟨8, [8, 5, 6, 4, 5], 3, []⟩])],
  [
    ((0, 1, 7), [GGTWNKill.tv ⟨8, [], 8, [0]⟩, GGTWNKill.line ⟨0, [9, 7, 8, 1], 2, []⟩,
        GGTWNKill.tv ⟨8, [], 8, [7]⟩, GGTWNKill.tv ⟨9, [], 9, [7]⟩, GGTWNKill.tv ⟨0, [], 1, [9, 6,
        5, 4, 3, 2]⟩]),
    ((0, 1, 0), [GGTWNKill.tv ⟨8, [], 8, [0]⟩, GGTWNKill.line ⟨0, [8, 9, 7, 8, 1], 0, []⟩,
        GGTWNKill.tv ⟨8, [], 8, [7]⟩, GGTWNKill.tv ⟨8, [], 8, [9, 0, 9]⟩]),
    ((0, 6, 2), [GGTWNKill.line ⟨0, [9, 8, 1], 2, []⟩, GGTWNKill.tv ⟨0, [], 0, [9]⟩,
        GGTWNKill.tv ⟨0, [], 0, [8, 7, 8]⟩, GGTWNKill.tv ⟨9, [], 9, [7]⟩, GGTWNKill.tv ⟨0, [], 1,
        [8, 6, 5, 4, 3, 2]⟩]),
    ((0, 6, 0), [GGTWNKill.line ⟨0, [8, 9, 7, 6, 8], 1, []⟩, GGTWNKill.tv ⟨0, [], 0, [8, 7, 8]⟩,
        GGTWNKill.tv ⟨7, [], 8, []⟩, GGTWNKill.tv ⟨0, [], 0, [8, 9, 8]⟩, GGTWNKill.tv ⟨7, [], 8,
        [9]⟩]),
    ((1, 0, 6), [GGTWNKill.tv ⟨6, [], 6, [9]⟩, GGTWNKill.line ⟨0, [9, 7, 5, 6, 8], 0, []⟩,
        GGTWNKill.tv ⟨6, [], 7, [9]⟩, GGTWNKill.tv ⟨7, [], 7, [8]⟩, GGTWNKill.line ⟨7, [9, 8], 0,
        []⟩]),
    ((1, 0, 0), [GGTWNKill.line ⟨0, [8, 9, 7, 6, 8], 1, []⟩, GGTWNKill.tv ⟨7, [], 7, [9]⟩,
        GGTWNKill.tv ⟨8, [], 8, [9, 7, 9]⟩, GGTWNKill.tv ⟨8, [], 8, [6]⟩]),
    ((1, 5, 1), [GGTWNKill.tv ⟨6, [], 6, [8]⟩, GGTWNKill.line ⟨9, [8, 7], 0, []⟩, GGTWNKill.tv ⟨6,
        [], 7, [8]⟩, GGTWNKill.line ⟨0, [8, 5, 6, 9], 0, []⟩, GGTWNKill.tv ⟨7, [], 7, [9]⟩]),
    ((1, 5, 0), [GGTWNKill.tv ⟨9, [], 9, [7]⟩, GGTWNKill.tv ⟨6, [], 6, [8]⟩, GGTWNKill.tv ⟨8, [],
        9, [6, 7]⟩, GGTWNKill.line ⟨4, [8, 9, 5, 8, 6, 5], 3, []⟩])],
  [
    ((0, 1, 1, 1), [(([0, 1, 2, 0, 1, 2, 0, 1], [2, 0, 0, 0, 0, 0, 1, 2]), GGTWLReason.hk ⟨0, [7,
        8, 1], 1, []⟩), (([0, 1, 2, 0, 1, 2, 0, 2], [2, 0, 0, 0, 0, 0, 1, 1]), GGTWLReason.hk ⟨0,
        [7, 8, 1], 1, []⟩)]),
    ((0, 2, 1, 1), [(([2, 1, 1, 1, 1, 1, 1, 1], [0, 2, 0, 0, 0, 0, 1, 2]), GGTWLReason.out8 ⟨[([0,
        2, 2, 1, 1, 1, 0, 1], [1, 2, 1, 2, 0, 1, 2, 2]), ([0, 0, 1, 1, 1, 2, 0, 2], [0, 2, 1, 0,
        2, 0, 1, 1]), ([0, 1, 1, 1, 1, 1, 2, 2], [2, 1, 0, 0, 0, 2, 0, 1]), ([0, 0, 0, 1, 1, 1, 0,
        0], [0, 0, 2, 1, 0, 1, 2, 0]), ([2, 1, 0, 2, 2, 1, 1, 2], [0, 0, 0, 2, 1, 2, 1, 1]), ([1,
        1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 1, 2, 0, 0, 0]), ([1, 2, 0, 1, 0, 1, 2, 0], [0, 0, 0, 2,
        1, 0, 0, 0]), ([2, 2, 2, 1, 0, 2, 1, 2], [2, 0, 1, 0, 0, 0, 0, 1])], [[6, 5, 6], [5, 6, 4,
        5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5], [1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1,
        3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4,
        3, 1], [7, 6, 5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5, 6, 7], [5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5],
        [6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7, 6],
        [4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1,
        6, 5, 4, 3, 2, 7, 6, 5, 4], [3, 2, 0, 2, 3], [4, 3, 1, 3, 4]], [[7, 8, 3, 2, 1, 2, 3, 8,
        7], [8, 5, 6, 7, 3, 2, 8, 0, 8, 2, 3, 7, 6, 5, 8], [8, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6,
        8], [6, 5, 4, 5, 6], [7, 4, 3, 2, 8, 0, 8, 2, 3, 4, 7], [4, 3, 2, 1, 2, 3, 4], [4, 3, 2,
        1, 0, 1, 2, 3, 4], [3, 4, 5, 6, 7, 8, 0, 8, 7, 6, 5, 4, 3]]⟩), (([2, 1, 1, 1, 1, 1, 1, 2],
        [0, 2, 0, 0, 0, 0, 1, 1]), GGTWLReason.out8 ⟨[([0, 2, 2, 1, 1, 1, 0, 2], [1, 2, 1, 2, 0,
        1, 2, 1]), ([0, 0, 1, 1, 1, 2, 0, 1], [0, 2, 1, 0, 2, 0, 1, 2]), ([0, 1, 1, 1, 1, 1, 2,
        1], [2, 1, 0, 0, 0, 2, 0, 2]), ([0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 2, 1, 0, 1, 2, 0]), ([2,
        1, 0, 2, 2, 1, 1, 1], [0, 0, 0, 2, 1, 2, 1, 2]), ([1, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 1,
        2, 0, 0, 0]), ([1, 2, 0, 1, 0, 1, 2, 0], [0, 0, 0, 2, 1, 0, 0, 0]), ([2, 2, 2, 1, 0, 2, 1,
        1], [2, 0, 1, 0, 0, 0, 0, 2])], [[6, 5, 6], [5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        5, 4, 6, 5], [1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3,
        1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1], [7, 6, 5, 4, 1, 3, 2, 0, 2,
        3, 1, 4, 5, 6, 7], [5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5], [6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7, 6], [4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4,
        5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 7, 6, 5, 4], [3, 2,
        0, 2, 3], [4, 3, 1, 3, 4]], [[7, 8, 3, 2, 1, 2, 3, 8, 7], [8, 5, 6, 7, 3, 2, 8, 0, 8, 2,
        3, 7, 6, 5, 8], [8, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 8], [6, 5, 4, 5, 6], [7, 4, 3, 2, 8,
        0, 8, 2, 3, 4, 7], [4, 3, 2, 1, 2, 3, 4], [4, 3, 2, 1, 0, 1, 2, 3, 4], [3, 4, 5, 6, 7, 8,
        0, 8, 7, 6, 5, 4, 3]]⟩), (([0, 0, 1, 2, 0, 1, 2, 1], [0, 2, 0, 0, 0, 0, 0, 2]),
        GGTWLReason.out8 ⟨[([0, 1, 2, 0, 1, 2, 0, 1], [2, 0, 0, 0, 0, 0, 1, 2]), ([0, 0, 0, 0, 2,
        1, 1, 1], [0, 0, 0, 1, 0, 2, 1, 2]), ([1, 1, 1, 1, 1, 1, 2, 2], [1, 0, 0, 0, 0, 2, 0, 1]),
        ([2, 1, 1, 1, 1, 1, 0, 1], [0, 2, 0, 0, 0, 1, 2, 2]), ([0, 0, 2, 1, 1, 1, 1, 1], [0, 1, 0,
        2, 0, 0, 1, 2]), ([0, 1, 1, 2, 2, 2, 2, 2], [2, 1, 2, 1, 0, 0, 2, 1]), ([0, 0, 1, 0, 0, 0,
        0, 0], [0, 2, 2, 2, 0, 0, 0, 0]), ([1, 1, 1, 2, 2, 0, 0, 2], [1, 0, 2, 1, 2, 1, 0, 1])],
        [[3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
        [5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5], [5, 4, 5], [6], [7, 5, 6, 1, 3,
        4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 7], [7, 6, 5, 4, 3, 2, 1,
        3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4,
        3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 4, 5, 6, 7],
        [4, 1, 3, 2, 0, 2, 3, 1, 4], [3, 2, 0, 2, 3]], [[8, 7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7, 8],
        [8, 2, 3, 1, 2, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8, 2, 1, 3, 2, 8], [6, 5, 4, 3,
        2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6], [8, 6, 5, 4, 3, 2,
        1, 0, 1, 2, 3, 4, 5, 6, 8], [2, 3, 1, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7,
        8, 2, 1, 3, 2], [3, 1, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 1, 3],
        [3], [3, 2, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 2, 3]]⟩), (([0, 0, 1, 2, 0, 1, 2, 2],
        [0, 2, 0, 0, 0, 0, 0, 1]), GGTWLReason.out8 ⟨[([0, 1, 2, 0, 1, 2, 0, 2], [2, 0, 0, 0, 0,
        0, 1, 1]), ([0, 0, 0, 0, 2, 1, 1, 2], [0, 0, 0, 1, 0, 2, 1, 1]), ([1, 1, 1, 1, 1, 1, 2,
        1], [1, 0, 0, 0, 0, 2, 0, 2]), ([2, 1, 1, 1, 1, 1, 0, 2], [0, 2, 0, 0, 0, 1, 2, 1]), ([0,
        0, 2, 1, 1, 1, 1, 2], [0, 1, 0, 2, 0, 0, 1, 1]), ([0, 1, 1, 2, 2, 2, 2, 1], [2, 1, 2, 1,
        0, 0, 2, 2]), ([0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 2, 0, 0, 0, 0]), ([1, 1, 1, 2, 2, 0, 0,
        1], [1, 0, 2, 1, 2, 1, 0, 2])], [[3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4,
        3, 2, 5, 4, 3, 1, 6, 5, 4, 3], [5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5],
        [5, 4, 5], [6], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1,
        6, 5, 7], [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6,
        7], [7, 6, 5, 4, 3, 4, 5, 6, 7], [4, 1, 3, 2, 0, 2, 3, 1, 4], [3, 2, 0, 2, 3]], [[8, 7, 6,
        5, 4, 3, 2, 3, 4, 5, 6, 7, 8], [8, 2, 3, 1, 2, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6,
        8, 2, 1, 3, 2, 8], [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2,
        3, 4, 5, 6], [8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8], [2, 3, 1, 2, 8, 7, 6, 5, 4, 3,
        2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 1, 3, 2], [3, 1, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2,
        3, 4, 5, 6, 7, 8, 2, 1, 3], [3], [3, 2, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 2, 3]]⟩)]),
    ((0, 3, 1, 1), [(([2, 1, 0, 0, 0, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2]), GGTWLReason.out8 ⟨[([0,
        2, 1, 1, 1, 0, 0, 1], [1, 0, 2, 0, 1, 2, 0, 2]), ([0, 0, 2, 1, 1, 1, 1, 1], [0, 1, 0, 2,
        0, 0, 1, 2]), ([1, 2, 0, 1, 1, 2, 0, 1], [0, 0, 0, 1, 2, 0, 1, 2]), ([2, 2, 2, 2, 2, 2, 2,
        0], [2, 0, 0, 0, 0, 0, 2, 0]), ([0, 2, 2, 1, 0, 2, 1, 2], [1, 2, 1, 0, 0, 0, 0, 1]), ([1,
        2, 2, 0, 1, 2, 2, 1], [0, 1, 2, 0, 0, 1, 2, 2]), ([0, 0, 1, 1, 2, 2, 0, 2], [0, 2, 1, 2,
        1, 2, 1, 1]), ([2, 2, 1, 1, 0, 2, 1, 2], [2, 1, 2, 1, 0, 0, 0, 1])], [[5, 6, 4, 5, 2, 3,
        4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6,
        7], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 7], [6,
        4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6], [6, 5, 4, 3, 1, 3, 4, 5, 6], [6, 7, 5, 6, 4, 5,
        3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7, 6], [6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5,
        2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6], [5, 4, 3, 4,
        5], [4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4,
        3, 1, 6, 5, 4, 3, 2, 7, 6, 5, 4]], [[8, 5, 4, 3, 2, 1, 2, 3, 4, 5, 8], [2, 3, 8, 7, 6, 5,
        4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8, 3, 2], [7, 6, 4, 5, 3, 4, 2, 3, 8, 0, 8, 3, 2, 4, 3, 5,
        4, 6, 7], [7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7], [8, 1, 0, 1, 8], [6, 5, 4, 2, 3, 8, 0,
        8, 3, 2, 4, 5, 6], [4, 2, 3, 8, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 8, 3, 2, 4], [3, 8, 0, 8,
        3]]⟩), (([2, 1, 0, 0, 0, 0, 0, 2], [0, 0, 2, 0, 0, 0, 0, 1]), GGTWLReason.out8 ⟨[([0, 2,
        1, 1, 1, 0, 0, 2], [1, 0, 2, 0, 1, 2, 0, 1]), ([0, 0, 2, 1, 1, 1, 1, 2], [0, 1, 0, 2, 0,
        0, 1, 1]), ([1, 2, 0, 1, 1, 2, 0, 2], [0, 0, 0, 1, 2, 0, 1, 1]), ([2, 2, 2, 2, 2, 2, 2,
        0], [2, 0, 0, 0, 0, 0, 2, 0]), ([0, 2, 2, 1, 0, 2, 1, 1], [1, 2, 1, 0, 0, 0, 0, 2]), ([1,
        2, 2, 0, 1, 2, 2, 2], [0, 1, 2, 0, 0, 1, 2, 1]), ([0, 0, 1, 1, 2, 2, 0, 1], [0, 2, 1, 2,
        1, 2, 1, 2]), ([2, 2, 1, 1, 0, 2, 1, 1], [2, 1, 2, 1, 0, 0, 0, 2])], [[5, 6, 4, 5, 2, 3,
        4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6,
        7], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 7], [6,
        4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6], [6, 5, 4, 3, 1, 3, 4, 5, 6], [6, 7, 5, 6, 4, 5,
        3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7, 6], [6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5,
        2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6], [5, 4, 3, 4,
        5], [4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4,
        3, 1, 6, 5, 4, 3, 2, 7, 6, 5, 4]], [[8, 5, 4, 3, 2, 1, 2, 3, 4, 5, 8], [2, 3, 8, 7, 6, 5,
        4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8, 3, 2], [7, 6, 4, 5, 3, 4, 2, 3, 8, 0, 8, 3, 2, 4, 3, 5,
        4, 6, 7], [7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7], [8, 1, 0, 1, 8], [6, 5, 4, 2, 3, 8, 0,
        8, 3, 2, 4, 5, 6], [4, 2, 3, 8, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 8, 3, 2, 4], [3, 8, 0, 8,
        3]]⟩)]),
    ((0, 4, 1, 1), [(([0, 0, 0, 0, 1, 2, 0, 1], [0, 0, 0, 2, 0, 0, 1, 2]), GGTWLReason.out8 ⟨[([0,
        1, 1, 1, 2, 0, 0, 1], [2, 1, 0, 2, 0, 1, 0, 2]), ([1, 2, 0, 0, 0, 1, 2, 2], [0, 0, 1, 0,
        2, 0, 0, 1]), ([0, 2, 1, 0, 2, 1, 1, 1], [1, 0, 0, 0, 0, 2, 1, 2]), ([0, 0, 0, 1, 1, 1, 0,
        0], [0, 0, 2, 1, 0, 1, 2, 0]), ([2, 2, 2, 1, 1, 0, 0, 2], [2, 0, 1, 2, 1, 2, 0, 1]), ([0,
        2, 2, 2, 2, 0, 0, 0], [1, 2, 0, 0, 2, 1, 0, 0]), ([1, 2, 2, 0, 1, 1, 2, 2], [0, 1, 2, 0,
        1, 2, 0, 1]), ([2, 2, 2, 2, 1, 1, 1, 2], [2, 0, 0, 1, 2, 0, 1, 1])], [[7, 4, 5, 6, 3, 4,
        5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7], [7, 6, 4, 5, 3, 4, 1, 3,
        2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 7], [6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6], [6, 7, 5, 6, 3, 4, 5, 2, 3, 4,
        1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 7, 6], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3,
        5, 6, 7], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5,
        7], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5], [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0,
        2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3], [3, 4, 2, 3, 1, 3, 2, 4, 3]], [[8, 6, 5, 4, 3,
        2, 3, 4, 5, 6, 8], [5, 4, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8, 4, 5], [1, 2, 3, 4,
        8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 4, 3, 2, 1], [6, 5, 4, 5, 6], [4, 8, 6, 5, 4, 3, 2,
        1, 2, 3, 4, 5, 6, 8, 4], [5, 4, 3, 2, 3, 4, 5], [3, 4, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4,
        5, 6, 8, 4, 3], [7, 8, 5, 4, 3, 2, 1, 2, 3, 4, 5, 8, 7]]⟩), (([0, 0, 0, 0, 1, 2, 0, 2],
        [0, 0, 0, 2, 0, 0, 1, 1]), GGTWLReason.out8 ⟨[([0, 1, 1, 1, 2, 0, 0, 2], [2, 1, 0, 2, 0,
        1, 0, 1]), ([1, 2, 0, 0, 0, 1, 2, 1], [0, 0, 1, 0, 2, 0, 0, 2]), ([0, 2, 1, 0, 2, 1, 1,
        2], [1, 0, 0, 0, 0, 2, 1, 1]), ([0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 2, 1, 0, 1, 2, 0]), ([2,
        2, 2, 1, 1, 0, 0, 1], [2, 0, 1, 2, 1, 2, 0, 2]), ([0, 2, 2, 2, 2, 0, 0, 0], [1, 2, 0, 0,
        2, 1, 0, 0]), ([1, 2, 2, 0, 1, 1, 2, 1], [0, 1, 2, 0, 1, 2, 0, 2]), ([2, 2, 2, 2, 1, 1, 1,
        1], [2, 0, 0, 1, 2, 0, 1, 2])], [[7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        2, 5, 4, 3, 6, 5, 4, 7], [7, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 7], [6, 7,
        0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4,
        3, 2, 0, 7, 6], [6, 7, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6,
        5, 7, 6], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6, 7], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 7], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5],
        [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
        [3, 4, 2, 3, 1, 3, 2, 4, 3]], [[8, 6, 5, 4, 3, 2, 3, 4, 5, 6, 8], [5, 4, 8, 6, 5, 4, 3, 2,
        1, 0, 1, 2, 3, 4, 5, 6, 8, 4, 5], [1, 2, 3, 4, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 4,
        3, 2, 1], [6, 5, 4, 5, 6], [4, 8, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 8, 4], [5, 4, 3, 2, 3,
        4, 5], [3, 4, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8, 4, 3], [7, 8, 5, 4, 3, 2, 1, 2,
        3, 4, 5, 8, 7]]⟩)]),
    ((0, 5, 1, 1), [(([2, 1, 0, 2, 1, 1, 1, 1], [0, 0, 0, 0, 2, 0, 1, 2]), GGTWLReason.out8 ⟨[([2,
        2, 2, 1, 1, 1, 1, 2], [2, 0, 1, 2, 0, 0, 1, 1]), ([0, 2, 2, 1, 0, 0, 0, 2], [1, 2, 1, 0,
        2, 0, 0, 1]), ([1, 2, 2, 2, 2, 2, 2, 1], [0, 1, 0, 0, 0, 0, 2, 2]), ([0, 0, 1, 2, 0, 0, 0,
        1], [0, 2, 0, 0, 1, 0, 0, 2]), ([0, 0, 2, 2, 2, 0, 0, 0], [0, 1, 2, 0, 2, 1, 0, 0]), ([2,
        2, 2, 2, 1, 0, 0, 2], [2, 0, 0, 1, 0, 2, 0, 1]), ([1, 1, 1, 1, 1, 1, 1, 0], [1, 0, 0, 0,
        0, 0, 1, 0]), ([2, 1, 0, 2, 2, 1, 0, 1], [0, 0, 0, 2, 1, 0, 2, 2])], [[7, 5, 6, 4, 5, 3,
        4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7], [5, 4, 3, 2, 0, 2, 3, 4, 5], [3, 1, 3], [1,
        3, 2, 0, 2, 3, 1], [5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5], [4, 5, 6, 1, 3, 4,
        5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4], [4, 3, 2, 1, 3, 4, 5, 6,
        7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5,
        4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4], [7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 7], [3, 2, 3]], [[7, 4, 5, 8, 0, 8, 5, 4,
        7], [5, 6, 4, 5, 8, 1, 0, 1, 8, 5, 4, 6, 5], [7, 2, 3, 4, 5, 8, 0, 8, 5, 4, 3, 2, 7], [5,
        6, 4, 5, 8, 2, 1, 0, 1, 2, 8, 5, 4, 6, 5], [5, 4, 3, 4, 5], [6, 5, 8, 0, 8, 5, 6], [7, 6,
        5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7], [7, 8, 5, 8, 7]]⟩), (([2, 1, 0, 2, 1, 1, 1, 2], [0, 0,
        0, 0, 2, 0, 1, 1]), GGTWLReason.out8 ⟨[([2, 2, 2, 1, 1, 1, 1, 1], [2, 0, 1, 2, 0, 0, 1,
        2]), ([0, 2, 2, 1, 0, 0, 0, 1], [1, 2, 1, 0, 2, 0, 0, 2]), ([1, 2, 2, 2, 2, 2, 2, 2], [0,
        1, 0, 0, 0, 0, 2, 1]), ([0, 0, 1, 2, 0, 0, 0, 2], [0, 2, 0, 0, 1, 0, 0, 1]), ([0, 0, 2, 2,
        2, 0, 0, 0], [0, 1, 2, 0, 2, 1, 0, 0]), ([2, 2, 2, 2, 1, 0, 0, 1], [2, 0, 0, 1, 0, 2, 0,
        2]), ([1, 1, 1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0, 1, 0]), ([2, 1, 0, 2, 2, 1, 0, 2], [0,
        0, 0, 2, 1, 0, 2, 1])], [[7, 5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7],
        [5, 4, 3, 2, 0, 2, 3, 4, 5], [3, 1, 3], [1, 3, 2, 0, 2, 3, 1], [5, 6, 4, 5, 3, 4, 2, 3, 1,
        3, 2, 4, 3, 5, 4, 6, 5], [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5,
        4, 3, 1, 6, 5, 4], [4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4], [7,
        2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3,
        2, 7], [3, 2, 3]], [[7, 4, 5, 8, 0, 8, 5, 4, 7], [5, 6, 4, 5, 8, 1, 0, 1, 8, 5, 4, 6, 5],
        [7, 2, 3, 4, 5, 8, 0, 8, 5, 4, 3, 2, 7], [5, 6, 4, 5, 8, 2, 1, 0, 1, 2, 8, 5, 4, 6, 5],
        [5, 4, 3, 4, 5], [6, 5, 8, 0, 8, 5, 6], [7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7], [7, 8, 5,
        8, 7]]⟩), (([0, 0, 0, 0, 0, 1, 2, 1], [0, 0, 0, 0, 2, 0, 0, 2]), GGTWLReason.out8 ⟨[([0,
        0, 0, 1, 2, 0, 0, 1], [0, 0, 2, 0, 0, 1, 0, 2]), ([1, 2, 2, 2, 2, 0, 0, 1], [0, 1, 0, 0,
        2, 1, 0, 2]), ([2, 2, 1, 0, 2, 1, 1, 1], [2, 1, 0, 0, 0, 2, 1, 2]), ([0, 0, 1, 1, 2, 2, 2,
        1], [0, 2, 1, 2, 1, 0, 2, 2]), ([1, 1, 1, 2, 2, 2, 0, 1], [1, 0, 2, 1, 0, 2, 1, 2]), ([2,
        1, 0, 2, 1, 1, 0, 1], [0, 0, 0, 0, 2, 1, 2, 2]), ([0, 0, 0, 0, 0, 2, 1, 2], [0, 0, 0, 0,
        1, 0, 0, 1]), ([0, 0, 1, 1, 1, 2, 0, 1], [0, 2, 1, 0, 2, 0, 1, 2])], [[4, 3, 1, 3, 4], [4,
        5, 6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5,
        4, 3, 7, 6, 5, 4], [7, 6, 5, 4, 3, 4, 5, 6, 7], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6,
        7], [3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1,
        4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3], [6, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6], [4, 3, 2, 3, 4], [7, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0,
        2, 3, 1, 4, 3, 2, 5, 4, 6, 7], [6]], [[6, 5, 8, 7, 6, 5, 4, 5, 6, 7, 8, 5, 6], [6, 2, 3,
        4, 5, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8, 5, 4, 3, 2, 6], [2, 3, 4, 5, 8, 7, 6,
        5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 5, 4, 3, 2], [5, 8, 6, 5, 4, 3, 4, 5, 6, 8, 5],
        [4, 5, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8, 5, 4], [8, 6, 5, 4, 3, 2, 1, 0, 1, 2,
        3, 4, 5, 6, 8], [8], [8, 7, 6, 5, 4, 3, 4, 5, 6, 7, 8]]⟩), (([0, 0, 0, 0, 0, 1, 2, 2], [0,
        0, 0, 0, 2, 0, 0, 1]), GGTWLReason.out8 ⟨[([0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 2, 0, 0, 1, 0,
        1]), ([1, 2, 2, 2, 2, 0, 0, 2], [0, 1, 0, 0, 2, 1, 0, 1]), ([2, 2, 1, 0, 2, 1, 1, 2], [2,
        1, 0, 0, 0, 2, 1, 1]), ([0, 0, 1, 1, 2, 2, 2, 2], [0, 2, 1, 2, 1, 0, 2, 1]), ([1, 1, 1, 2,
        2, 2, 0, 2], [1, 0, 2, 1, 0, 2, 1, 1]), ([2, 1, 0, 2, 1, 1, 0, 2], [0, 0, 0, 0, 2, 1, 2,
        1]), ([0, 0, 0, 0, 0, 2, 1, 1], [0, 0, 0, 0, 1, 0, 0, 2]), ([0, 0, 1, 1, 1, 2, 0, 2], [0,
        2, 1, 0, 2, 0, 1, 1])], [[4, 3, 1, 3, 4], [4, 5, 6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 7, 6, 5, 4], [7, 6, 5, 4, 3, 4, 5, 6,
        7], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6, 7], [3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5,
        6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6,
        5, 4, 3, 1, 2, 3], [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6], [4, 3,
        2, 3, 4], [7, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 7], [6]], [[6, 5,
        8, 7, 6, 5, 4, 5, 6, 7, 8, 5, 6], [6, 2, 3, 4, 5, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6,
        7, 8, 5, 4, 3, 2, 6], [2, 3, 4, 5, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 5,
        4, 3, 2], [5, 8, 6, 5, 4, 3, 4, 5, 6, 8, 5], [4, 5, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6,
        7, 8, 5, 4], [8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8], [8], [8, 7, 6, 5, 4, 3, 4, 5,
        6, 7, 8]]⟩)]),
    ((0, 6, 1, 1), [(([2, 1, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 2]), GGTWLReason.hk ⟨0, [7,
        6, 8], 0, []⟩), (([2, 1, 0, 2, 1, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 1]), GGTWLReason.hk ⟨0,
        [7, 6, 8], 0, []⟩)]),
    ((1, 0, 1, 1), [(([1, 2, 0, 1, 2, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2]), GGTWLReason.hk ⟨5, [6,
        8, 7, 6], 0, []⟩), (([1, 2, 0, 1, 2, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1]),
        GGTWLReason.hk ⟨5, [6, 8, 7, 6], 0, []⟩)]),
    ((1, 1, 1, 1), [(([0, 1, 2, 0, 1, 2, 0, 1], [2, 0, 0, 0, 0, 0, 1, 2]), GGTWLReason.out8 ⟨[([2,
        2, 1, 1, 1, 0, 0, 1], [2, 1, 2, 0, 1, 2, 0, 2]), ([0, 1, 1, 1, 1, 2, 0, 2], [2, 1, 0, 0,
        2, 0, 1, 1]), ([0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 2, 0, 0, 0, 0]), ([0, 0, 0, 1, 1, 1, 0,
        0], [0, 0, 2, 1, 0, 1, 2, 0]), ([0, 2, 1, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 2]), ([0,
        0, 1, 2, 2, 2, 0, 2], [0, 2, 0, 1, 0, 2, 1, 1]), ([0, 0, 2, 1, 0, 2, 1, 2], [0, 1, 0, 0,
        0, 0, 0, 1]), ([1, 2, 0, 1, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0])], [[0, 2, 3, 4, 5, 6,
        1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0], [1, 3,
        2, 0, 2, 3, 1], [5, 4, 3, 2, 3, 4, 5], [2], [5, 6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 7, 6, 5], [1, 3, 4, 5, 6, 7, 2, 3, 4,
        5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 7, 6,
        5, 4, 3, 1], [3, 4, 2, 3, 1, 3, 2, 4, 3], [7, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4,
        3, 2, 5, 4, 3, 6, 7], [6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5,
        4, 3, 6, 5, 4, 7, 6]], [[6, 7, 8, 2, 1, 0, 1, 2, 8, 7, 6], [7, 1, 8, 5, 4, 3, 2, 1, 0, 1,
        2, 3, 4, 5, 8, 1, 7], [3], [6, 5, 4, 5, 6], [4, 5, 6, 7, 1, 8, 2, 1, 0, 1, 2, 8, 1, 7, 6,
        5, 4], [7, 2, 1, 8, 3, 2, 1, 0, 1, 2, 3, 8, 1, 2, 7], [8, 7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7,
        8], [7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7]]⟩), (([0, 1, 2, 0, 1, 2, 0, 2], [2, 0,
        0, 0, 0, 0, 1, 1]), GGTWLReason.out8 ⟨[([2, 2, 1, 1, 1, 0, 0, 2], [2, 1, 2, 0, 1, 2, 0,
        1]), ([0, 1, 1, 1, 1, 2, 0, 1], [2, 1, 0, 0, 2, 0, 1, 2]), ([0, 0, 1, 0, 0, 0, 0, 0], [0,
        2, 2, 2, 0, 0, 0, 0]), ([0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 2, 1, 0, 1, 2, 0]), ([0, 2, 1, 0,
        0, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 1]), ([0, 0, 1, 2, 2, 2, 0, 1], [0, 2, 0, 1, 0, 2, 1,
        2]), ([0, 0, 2, 1, 0, 2, 1, 1], [0, 1, 0, 0, 0, 0, 0, 2]), ([1, 2, 0, 1, 2, 0, 1, 0], [0,
        0, 0, 0, 0, 0, 2, 0])], [[0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4,
        3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0], [1, 3, 2, 0, 2, 3, 1], [5, 4, 3, 2, 3, 4, 5], [2],
        [5, 6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5,
        4, 3, 7, 6, 5], [1, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3,
        1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 7, 6, 5, 4, 3, 1], [3, 4, 2, 3, 1, 3, 2, 4, 3], [7,
        6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 7], [6, 7, 4, 5, 6, 3, 4,
        5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7, 6]], [[6, 7, 8, 2, 1, 0, 1,
        2, 8, 7, 6], [7, 1, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 1, 7], [3], [6, 5, 4, 5, 6],
        [4, 5, 6, 7, 1, 8, 2, 1, 0, 1, 2, 8, 1, 7, 6, 5, 4], [7, 2, 1, 8, 3, 2, 1, 0, 1, 2, 3, 8,
        1, 2, 7], [8, 7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7, 8], [7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5,
        6, 7]]⟩), (([0, 1, 2, 0, 1, 2, 2, 1], [2, 0, 0, 0, 0, 1, 2, 2]), GGTWLReason.out8 ⟨[([0,
        2, 2, 1, 0, 2, 1, 2], [1, 2, 1, 0, 0, 0, 0, 1]), ([0, 2, 1, 0, 0, 0, 0, 1], [1, 0, 0, 2,
        0, 0, 0, 2]), ([0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0]), ([0, 1, 2, 2, 0, 0, 0,
        2], [2, 0, 1, 2, 1, 0, 0, 1]), ([2, 1, 1, 1, 0, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 2]), ([1,
        2, 2, 2, 2, 2, 0, 2], [0, 1, 0, 0, 0, 2, 1, 1]), ([0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0,
        2, 2, 2, 0]), ([1, 1, 2, 0, 1, 1, 2, 1], [1, 2, 0, 0, 1, 2, 0, 2])], [[7, 6, 5, 6, 7], [7,
        6, 5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5, 6, 7], [7, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        5, 4, 6, 7], [2], [3, 1, 3], [6, 5, 4, 5, 6], [6], [5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3,
        4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0,
        7, 6, 5, 4, 3, 1, 2, 3, 4, 5], [5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5]], [[8, 6, 5, 4, 3, 4, 5,
        6, 8], [4, 5, 6, 1, 8, 2, 1, 0, 1, 2, 8, 1, 6, 5, 4], [3], [5, 6, 1, 8, 2, 1, 0, 1, 2, 8,
        1, 6, 5], [5, 6, 8, 1, 0, 1, 8, 6, 5], [8, 1, 0, 1, 8], [6], [6, 8, 1, 8, 6]]⟩), (([0, 1,
        2, 0, 1, 2, 2, 2], [2, 0, 0, 0, 0, 1, 2, 1]), GGTWLReason.out8 ⟨[([0, 2, 2, 1, 0, 2, 1,
        1], [1, 2, 1, 0, 0, 0, 0, 2]), ([0, 2, 1, 0, 0, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 1]), ([0,
        0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0]), ([0, 1, 2, 2, 0, 0, 0, 1], [2, 0, 1, 2,
        1, 0, 0, 2]), ([2, 1, 1, 1, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 1]), ([1, 2, 2, 2, 2, 2, 0,
        1], [0, 1, 0, 0, 0, 2, 1, 2]), ([0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 2, 2, 0]), ([1,
        1, 2, 0, 1, 1, 2, 2], [1, 2, 0, 0, 1, 2, 0, 1])], [[7, 6, 5, 6, 7], [7, 6, 5, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 5, 6, 7], [7, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 7], [2],
        [3, 1, 3], [6, 5, 4, 5, 6], [6], [5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4,
        5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1,
        2, 3, 4, 5], [5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5]], [[8, 6, 5, 4, 3, 4, 5, 6, 8], [4, 5, 6,
        1, 8, 2, 1, 0, 1, 2, 8, 1, 6, 5, 4], [3], [5, 6, 1, 8, 2, 1, 0, 1, 2, 8, 1, 6, 5], [5, 6,
        8, 1, 0, 1, 8, 6, 5], [8, 1, 0, 1, 8], [6], [6, 8, 1, 8, 6]]⟩)]),
    ((1, 2, 1, 1), [(([0, 0, 1, 2, 0, 1, 2, 1], [0, 2, 0, 0, 0, 0, 0, 2]), GGTWLReason.out8 ⟨[([0,
        1, 2, 0, 1, 2, 0, 1], [2, 0, 0, 0, 0, 0, 1, 2]), ([0, 0, 0, 0, 2, 1, 1, 1], [0, 0, 0, 1,
        0, 2, 1, 2]), ([1, 1, 1, 1, 1, 1, 2, 2], [1, 0, 0, 0, 0, 2, 0, 1]), ([2, 1, 1, 1, 1, 1, 0,
        1], [0, 2, 0, 0, 0, 1, 2, 2]), ([0, 0, 2, 1, 1, 1, 1, 1], [0, 1, 0, 2, 0, 0, 1, 2]), ([0,
        1, 1, 2, 2, 2, 2, 2], [2, 1, 2, 1, 0, 0, 2, 1]), ([0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 2,
        0, 0, 0, 0]), ([1, 1, 1, 2, 2, 0, 0, 2], [1, 0, 2, 1, 2, 1, 0, 1])], [[3, 4, 5, 6, 1, 3,
        4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3], [5, 6, 4, 5, 3, 4,
        1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5], [5, 4, 5], [6], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 7], [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0,
        2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3,
        2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 4, 5, 6, 7], [4, 1, 3, 2, 0, 2,
        3, 1, 4], [3, 2, 0, 2, 3]], [[8, 7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7, 8], [8, 2, 3, 1, 2, 8,
        6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8, 2, 1, 3, 2, 8], [6, 5, 4, 3, 2, 8, 7, 6, 5, 4,
        3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6], [8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4,
        5, 6, 8], [2, 3, 1, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 1, 3, 2], [3,
        1, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 1, 3], [3], [3, 2, 8, 5, 4, 3,
        2, 1, 0, 1, 2, 3, 4, 5, 8, 2, 3]]⟩), (([0, 0, 1, 2, 0, 1, 2, 2], [0, 2, 0, 0, 0, 0, 0,
        1]), GGTWLReason.out8 ⟨[([0, 1, 2, 0, 1, 2, 0, 2], [2, 0, 0, 0, 0, 0, 1, 1]), ([0, 0, 0,
        0, 2, 1, 1, 2], [0, 0, 0, 1, 0, 2, 1, 1]), ([1, 1, 1, 1, 1, 1, 2, 1], [1, 0, 0, 0, 0, 2,
        0, 2]), ([2, 1, 1, 1, 1, 1, 0, 2], [0, 2, 0, 0, 0, 1, 2, 1]), ([0, 0, 2, 1, 1, 1, 1, 2],
        [0, 1, 0, 2, 0, 0, 1, 1]), ([0, 1, 1, 2, 2, 2, 2, 1], [2, 1, 2, 1, 0, 0, 2, 2]), ([0, 0,
        1, 0, 0, 0, 0, 0], [0, 2, 2, 2, 0, 0, 0, 0]), ([1, 1, 1, 2, 2, 0, 0, 1], [1, 0, 2, 1, 2,
        1, 0, 2])], [[3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1,
        6, 5, 4, 3], [5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5], [5, 4, 5], [6],
        [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 7], [7, 6,
        5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1,
        4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4,
        3, 4, 5, 6, 7], [4, 1, 3, 2, 0, 2, 3, 1, 4], [3, 2, 0, 2, 3]], [[8, 7, 6, 5, 4, 3, 2, 3,
        4, 5, 6, 7, 8], [8, 2, 3, 1, 2, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8, 2, 1, 3, 2,
        8], [6, 5, 4, 3, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 3, 4, 5, 6], [8,
        6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8], [2, 3, 1, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2,
        3, 4, 5, 6, 7, 8, 2, 1, 3, 2], [3, 1, 2, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7,
        8, 2, 1, 3], [3], [3, 2, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 2, 3]]⟩)]),
    ((1, 3, 1, 1), [(([0, 0, 0, 1, 2, 0, 0, 1], [0, 0, 2, 0, 0, 1, 0, 2]), GGTWLReason.out8 ⟨[([0,
        0, 0, 0, 2, 1, 1, 2], [0, 0, 0, 1, 0, 2, 1, 1]), ([1, 1, 2, 0, 1, 2, 0, 2], [1, 2, 0, 0,
        0, 0, 1, 1]), ([0, 0, 2, 2, 2, 0, 0, 0], [0, 1, 2, 0, 2, 1, 0, 0]), ([2, 1, 1, 0, 2, 1, 0,
        1], [0, 2, 1, 0, 0, 0, 2, 2]), ([1, 2, 2, 2, 0, 0, 0, 1], [0, 1, 0, 2, 1, 0, 0, 2]), ([2,
        2, 2, 0, 0, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0, 0]), ([0, 0, 0, 2, 2, 2, 0, 0], [0, 0, 1, 2,
        0, 2, 1, 0]), ([1, 1, 1, 2, 2, 2, 2, 1], [1, 0, 2, 1, 0, 0, 2, 2])], [[5, 6, 3, 4, 5, 2,
        3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5], [7, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 7], [3, 1, 3], [7, 5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2,
        3, 1, 4, 3, 2, 5, 4, 6, 5, 7], [6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6], [4, 5, 6, 7,
        3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 7,
        6, 5, 4], [6, 7, 5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7, 6], [6, 5, 4,
        1, 3, 2, 0, 2, 3, 1, 4, 5, 6], [5, 4, 2, 3, 1, 3, 2, 4, 5]], [[8, 7, 6, 5, 4, 5, 6, 7, 8],
        [8, 6, 3, 8, 4, 3, 2, 1, 2, 3, 4, 8, 3, 6, 8], [5, 4, 3, 4, 5], [7, 6, 3, 8, 4, 3, 2, 1,
        0, 1, 2, 3, 4, 8, 3, 6, 7], [2, 3, 8, 5, 4, 3, 2, 1, 2, 3, 4, 5, 8, 3, 2], [3, 2, 1, 2,
        3], [6, 5, 4, 5, 6], [7, 6, 8, 4, 3, 2, 1, 2, 3, 4, 8, 6, 7]]⟩), (([0, 0, 0, 1, 2, 0, 0,
        2], [0, 0, 2, 0, 0, 1, 0, 1]), GGTWLReason.out8 ⟨[([0, 0, 0, 0, 2, 1, 1, 1], [0, 0, 0, 1,
        0, 2, 1, 2]), ([1, 1, 2, 0, 1, 2, 0, 1], [1, 2, 0, 0, 0, 0, 1, 2]), ([0, 0, 2, 2, 2, 0, 0,
        0], [0, 1, 2, 0, 2, 1, 0, 0]), ([2, 1, 1, 0, 2, 1, 0, 2], [0, 2, 1, 0, 0, 0, 2, 1]), ([1,
        2, 2, 2, 0, 0, 0, 2], [0, 1, 0, 2, 1, 0, 0, 1]), ([2, 2, 2, 0, 0, 0, 0, 0], [2, 0, 2, 1,
        0, 0, 0, 0]), ([0, 0, 0, 2, 2, 2, 0, 0], [0, 0, 1, 2, 0, 2, 1, 0]), ([1, 1, 1, 2, 2, 2, 2,
        2], [1, 0, 2, 1, 0, 0, 2, 1])], [[5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5,
        4, 3, 6, 5], [7, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 7],
        [3, 1, 3], [7, 5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5, 7], [6, 4,
        5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6], [4, 5, 6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 7, 6, 5, 4], [6, 7, 5, 6, 4, 5, 3, 4,
        1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7, 6], [6, 5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5, 6], [5,
        4, 2, 3, 1, 3, 2, 4, 5]], [[8, 7, 6, 5, 4, 5, 6, 7, 8], [8, 6, 3, 8, 4, 3, 2, 1, 2, 3, 4,
        8, 3, 6, 8], [5, 4, 3, 4, 5], [7, 6, 3, 8, 4, 3, 2, 1, 0, 1, 2, 3, 4, 8, 3, 6, 7], [2, 3,
        8, 5, 4, 3, 2, 1, 2, 3, 4, 5, 8, 3, 2], [3, 2, 1, 2, 3], [6, 5, 4, 5, 6], [7, 6, 8, 4, 3,
        2, 1, 2, 3, 4, 8, 6, 7]]⟩)]),
    ((1, 4, 1, 1), [(([0, 0, 0, 0, 1, 2, 0, 1], [0, 0, 0, 2, 0, 0, 1, 2]), GGTWLReason.out8 ⟨[([0,
        1, 1, 1, 2, 0, 0, 1], [2, 1, 0, 2, 0, 1, 0, 2]), ([1, 2, 0, 0, 0, 1, 2, 2], [0, 0, 1, 0,
        2, 0, 0, 1]), ([0, 2, 1, 0, 2, 1, 1, 1], [1, 0, 0, 0, 0, 2, 1, 2]), ([0, 0, 0, 1, 1, 1, 0,
        0], [0, 0, 2, 1, 0, 1, 2, 0]), ([2, 2, 2, 1, 1, 0, 0, 2], [2, 0, 1, 2, 1, 2, 0, 1]), ([0,
        2, 2, 2, 2, 0, 0, 0], [1, 2, 0, 0, 2, 1, 0, 0]), ([1, 2, 2, 0, 1, 1, 2, 2], [0, 1, 2, 0,
        1, 2, 0, 1]), ([2, 2, 2, 2, 1, 1, 1, 2], [2, 0, 0, 1, 2, 0, 1, 1])], [[7, 4, 5, 6, 3, 4,
        5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7], [7, 6, 4, 5, 3, 4, 1, 3,
        2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 7], [6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2,
        0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6], [6, 7, 5, 6, 3, 4, 5, 2, 3, 4,
        1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 7, 6], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3,
        5, 6, 7], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5,
        7], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5], [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0,
        2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3], [3, 4, 2, 3, 1, 3, 2, 4, 3]], [[8, 6, 5, 4, 3,
        2, 3, 4, 5, 6, 8], [5, 4, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8, 4, 5], [1, 2, 3, 4,
        8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 4, 3, 2, 1], [6, 5, 4, 5, 6], [4, 8, 6, 5, 4, 3, 2,
        1, 2, 3, 4, 5, 6, 8, 4], [5, 4, 3, 2, 3, 4, 5], [3, 4, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4,
        5, 6, 8, 4, 3], [7, 8, 5, 4, 3, 2, 1, 2, 3, 4, 5, 8, 7]]⟩), (([0, 0, 0, 0, 1, 2, 0, 2],
        [0, 0, 0, 2, 0, 0, 1, 1]), GGTWLReason.out8 ⟨[([0, 1, 1, 1, 2, 0, 0, 2], [2, 1, 0, 2, 0,
        1, 0, 1]), ([1, 2, 0, 0, 0, 1, 2, 1], [0, 0, 1, 0, 2, 0, 0, 2]), ([0, 2, 1, 0, 2, 1, 1,
        2], [1, 0, 0, 0, 0, 2, 1, 1]), ([0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 2, 1, 0, 1, 2, 0]), ([2,
        2, 2, 1, 1, 0, 0, 1], [2, 0, 1, 2, 1, 2, 0, 2]), ([0, 2, 2, 2, 2, 0, 0, 0], [1, 2, 0, 0,
        2, 1, 0, 0]), ([1, 2, 2, 0, 1, 1, 2, 1], [0, 1, 2, 0, 1, 2, 0, 2]), ([2, 2, 2, 2, 1, 1, 1,
        1], [2, 0, 0, 1, 2, 0, 1, 2])], [[7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
        2, 5, 4, 3, 6, 5, 4, 7], [7, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 7], [6, 7,
        0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4,
        3, 2, 0, 7, 6], [6, 7, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6,
        5, 7, 6], [7, 6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6, 7], [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1,
        3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 7], [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5],
        [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
        [3, 4, 2, 3, 1, 3, 2, 4, 3]], [[8, 6, 5, 4, 3, 2, 3, 4, 5, 6, 8], [5, 4, 8, 6, 5, 4, 3, 2,
        1, 0, 1, 2, 3, 4, 5, 6, 8, 4, 5], [1, 2, 3, 4, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 4,
        3, 2, 1], [6, 5, 4, 5, 6], [4, 8, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 8, 4], [5, 4, 3, 2, 3,
        4, 5], [3, 4, 8, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 8, 4, 3], [7, 8, 5, 4, 3, 2, 1, 2,
        3, 4, 5, 8, 7]]⟩), (([0, 0, 0, 0, 1, 2, 2, 1], [0, 0, 0, 2, 0, 1, 2, 2]),
        GGTWLReason.out8 ⟨[([0, 1, 1, 1, 1, 1, 1, 0], [2, 1, 0, 0, 0, 0, 1, 0]), ([0, 1, 2, 0, 0,
        1, 2, 2], [2, 0, 0, 1, 2, 0, 0, 1]), ([0, 2, 2, 2, 1, 1, 0, 2], [1, 2, 0, 1, 2, 1, 2, 1]),
        ([2, 1, 0, 2, 2, 1, 1, 1], [0, 0, 0, 2, 1, 2, 1, 2]), ([1, 2, 2, 2, 2, 2, 2, 1], [0, 1, 0,
        0, 0, 0, 2, 2]), ([0, 0, 0, 1, 2, 0, 0, 1], [0, 0, 2, 0, 0, 1, 0, 2]), ([0, 0, 1, 0, 0, 0,
        0, 0], [0, 2, 2, 2, 0, 0, 0, 0]), ([0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 1, 1, 2, 0, 0])],
        [[3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4,
        3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3], [1, 3, 4, 5, 6, 7, 0, 2, 3,
        4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0,
        7, 6, 5, 4, 3, 1], [4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4], [6], [6, 5, 4, 3, 4, 5,
        6], [7, 6, 5, 4, 3, 4, 5, 6, 7], [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4,
        6, 5], [4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5,
        4, 3, 1, 6, 5, 4, 3, 2, 7, 6, 5, 4], [5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5]],
        [[7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7], [4, 8, 7, 3, 4, 8, 5, 4, 3, 2, 3, 4, 5, 8, 4, 3, 7, 8,
        4], [7, 8, 5, 4, 3, 2, 3, 4, 5, 8, 7], [7, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 7], [2,
        3, 4, 8, 5, 4, 3, 2, 1, 2, 3, 4, 5, 8, 4, 3, 2], [8, 7, 6, 5, 4, 5, 6, 7, 8], [3], [5, 4,
        5]]⟩), (([0, 0, 0, 0, 1, 2, 2, 2], [0, 0, 0, 2, 0, 1, 2, 1]), GGTWLReason.out8 ⟨[([0, 1,
        1, 1, 1, 1, 1, 0], [2, 1, 0, 0, 0, 0, 1, 0]), ([0, 1, 2, 0, 0, 1, 2, 1], [2, 0, 0, 1, 2,
        0, 0, 2]), ([0, 2, 2, 2, 1, 1, 0, 1], [1, 2, 0, 1, 2, 1, 2, 2]), ([2, 1, 0, 2, 2, 1, 1,
        2], [0, 0, 0, 2, 1, 2, 1, 1]), ([1, 2, 2, 2, 2, 2, 2, 2], [0, 1, 0, 0, 0, 0, 2, 1]), ([0,
        0, 0, 1, 2, 0, 0, 2], [0, 0, 2, 0, 0, 1, 0, 1]), ([0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 2,
        0, 0, 0, 0]), ([0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 1, 1, 2, 0, 0])], [[3, 2, 1, 3, 4, 5,
        6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6,
        5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3], [1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5,
        2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1],
        [4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4], [6], [6, 5, 4, 3, 4, 5, 6], [7, 6, 5, 4, 3,
        4, 5, 6, 7], [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5], [4, 5, 6, 7,
        2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3,
        2, 7, 6, 5, 4], [5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5]], [[7, 6, 5, 4, 3, 2,
        3, 4, 5, 6, 7], [4, 8, 7, 3, 4, 8, 5, 4, 3, 2, 3, 4, 5, 8, 4, 3, 7, 8, 4], [7, 8, 5, 4, 3,
        2, 3, 4, 5, 8, 7], [7, 8, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 8, 7], [2, 3, 4, 8, 5, 4, 3, 2,
        1, 2, 3, 4, 5, 8, 4, 3, 2], [8, 7, 6, 5, 4, 5, 6, 7, 8], [3], [5, 4, 5]]⟩)]),
    ((1, 5, 1, 1), [(([0, 0, 0, 0, 0, 1, 2, 1], [0, 0, 0, 0, 2, 0, 0, 2]), GGTWLReason.hk ⟨4, [6,
        5, 8, 7, 6, 5], 3, []⟩), (([0, 0, 0, 0, 0, 1, 2, 2], [0, 0, 0, 0, 2, 0, 0, 1]),
        GGTWLReason.hk ⟨4, [6, 5, 8, 7, 6, 5], 3, []⟩)])],
  [
    ]⟩

end Certificates.TwoDepSmallLow

end
