module

public import Certificates.Data.DepASmall

public section

namespace Certificates.TwoDepSmall

open Certificates.DepASmall

set_option compiler.extract_closed false

@[expose] def ggTWNX (N : Nat) : List Nat :=
  (List.range (N - 1)).map fun j => if j + 2 = N then 1 else 0

@[expose] def ggTWNH (p N i : Nat) : List Nat := (List.range (N - 1)).map fun j =>
  if j + 2 = N then 0
  else if i = 0 then (p - (j + 2) % p) % p
  else if j + 1 = i then 1 else 0

@[expose] def ggTWNA (p N i : Nat) : List Nat := (List.range (N - 1)).map fun j =>
  if j + 2 = N then 0
  else if j + 1 = i then 2 % p
  else if j + 2 = i || j = i then (p - 1) % p else 0

@[expose] def ggTWNZ (p N pos : Nat) : List Nat := (List.range (N - 1)).map fun j =>
  if pos = 0 then (if j + 2 = N then 0 else (j + 1) % p) else (if j + 3 = N then 1 else 0)

@[expose] def ggTWNInJ (N pos c : Nat) : Bool :=
  if pos = 0 then decide (1 ≤ c) && decide (c + 3 ≤ N) else decide (c + 4 ≤ N)

@[expose] def ggTWNPlace (pos c : Nat) : Nat := if pos = 0 then c - 1 else c

@[expose] def ggTWNAdd (p : Nat) (a b : List Nat) : List Nat :=
  List.zipWith (fun x y => (x + y) % p) a b

@[expose] def ggTWNRefl (p : Nat) (g : GGDepANPair) (v : List Nat) : List Nat :=
  ggDepANSub p v (ggDepANSmul p (ggDepANDot p g.2 v) g.1)

@[expose] def ggTWNGen (p N : Nat) (news : List GGDepANPair) (g : Nat) : GGDepANPair :=
  if g + 1 < N then (ggTWNH p N g, ggTWNA p N g) else news.getD (g + 1 - N) ([], [])

@[expose] def ggTWNWord (p N : Nat) (news : List GGDepANPair) (q : GGDepANPair) (w : List Nat) :
    GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj p acc (ggTWNGen p N news g)) q

@[expose] def ggTWNApply (p N : Nat) (w : List Nat) (v : List Nat) : List Nat :=
  w.foldr (fun g acc => ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) acc) v

structure GGTWNLine where
  g : Nat
  w : List Nat
  i : Nat
  wv : List Nat

inductive GGTWNKill
  | tv (w : GGDepANWit)
  | line (w : GGTWNLine)

@[expose] def ggTWNRoots (p N : Nat) : List (List Nat) :=
  (List.range (N - 1)).flatMap fun i => (List.range (N - 1)).flatMap fun j =>
    if i ≤ j then
      let v := ((List.range (N - 1)).filter fun k => decide (i ≤ k) && decide (k ≤ j)).foldl
        (fun acc k => ggTWNAdd p acc (ggTWNH p N k)) (List.replicate (N - 1) 0)
      [v, ggDepANSmul p (p - 1) v]
    else []

@[expose] def ggTWNRootsOK (p N : Nat) (R : List (List Nat)) : Bool :=
  (List.range (N - 1)).all (fun i => R.contains (ggTWNH p N i)) &&
  R.all (fun u => (ggDepANFirstNZ p (u.take (N - 2))).isSome) &&
  R.all fun u => (List.range (N - 1)).all fun g =>
    R.contains (ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) u)

@[expose] def ggTWNKillValid (N G : Nat) : GGTWNKill → Bool
  | .tv w => decide (w.g1 < G) && decide (w.g2 < G) && w.w1.all (fun g => decide (g < G)) &&
      w.w2.all fun g => decide (g < G)
  | .line w => decide (w.g < G) && w.w.all (fun g => decide (g < G)) && decide (w.i + 1 < N) &&
      w.wv.all fun g => decide (g + 1 < N)

@[expose] def ggTWNKillTest (p N : Nat) (news : List GGDepANPair) (R : List (List Nat)) :
    GGTWNKill → Bool
  | .tv w => ggDepANTestPair p (ggTWNWord p N news (ggTWNGen p N news w.g1) w.w1)
      (ggTWNWord p N news (ggTWNGen p N news w.g2) w.w2)
  | .line w =>
    let s := ggTWNWord p N news (ggTWNGen p N news w.g) w.w
    let sv := ggTWNRefl p s (ggTWNApply p N w.wv (ggTWNH p N w.i))
    ggDepANDot p s.2 (ggTWNX N) == 0 &&
      R.all fun u => !ggDepANPar p (u.take (N - 2)) (sv.take (N - 2))

@[expose] def ggTWNDecode (p : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => (k % p) :: ggTWNDecode p n (k / p)

@[expose] def ggTWNSolH (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  let As := (List.range (N - 1)).map fun c => ggTWNA p N c
  (List.range (p ^ (N - 1))).filterMap fun k =>
    let v := ggTWNDecode p (N - 1) k
    if (List.range (N - 1)).all (fun c =>
        !ggTWNInJ N pos c || ggDepANDot p (As.getD c []) v == tgt c % p) then some v else none

@[expose] def ggTWNSolA (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  let Hs := (List.range (N - 1)).map fun c => ggTWNH p N c
  (List.range (p ^ (N - 1))).filterMap fun k =>
    let v := ggTWNDecode p (N - 1) k
    if (List.range (N - 1)).all (fun c =>
        !ggTWNInJ N pos c || ggDepANDot p v (Hs.getD c []) == tgt c % p) then some v else none

@[expose] def ggTWNPat1B (N pos c0 mi ni : Nat) : Bool :=
  ggTWNInJ N pos c0 &&
    ((((ggTWNPlace pos c0 == 0) || decide (ggTWNPlace pos c0 + 1 = N - 3)) &&
        ((mi == 1 && ni == 1) || (mi == 1 && ni == 2) || (mi == 2 && ni == 1))) ||
      (decide (3 ≤ N - 3) &&
        ((ggTWNPlace pos c0 == 1) || decide (ggTWNPlace pos c0 + 2 = N - 3)) &&
        mi == 1 && ni == 1) ||
      (decide (5 ≤ N - 3) && decide (N - 3 ≤ 7) &&
        ((ggTWNPlace pos c0 == 2) || decide (ggTWNPlace pos c0 + 3 = N - 3)) &&
        mi == 1 && ni == 1))

@[expose] def ggTWNPat2B (N pos c : Nat) (c2 : Option Nat) : Bool :=
  ggTWNInJ N pos c &&
    ((ggTWNPlace pos c == 0) || decide (ggTWNPlace pos c + 1 = N - 3)) &&
    (match c2 with
      | none => true
      | some c' => ggTWNInJ N pos c' &&
          ((ggTWNPlace pos c == 0 && decide (ggTWNPlace pos c' + 1 = N - 3)) ||
            (decide (ggTWNPlace pos c + 1 = N - 3) && ggTWNPlace pos c' == 0)))

@[expose] def ggTWNCases1 (p N pos c0 mi ni : Nat) (R : List (List Nat)) (wits : List GGTWNKill) :
    Bool :=
  let X := ggTWNX N
  let has := ggTWNSolH p N pos fun c => if c = c0 then (p - ni % p) % p else 0
  let aas := ggTWNSolA p N pos fun c => if c = c0 then (p - mi % p) % p else 0
  has.all fun ha => aas.all fun aa =>
    if ggDepANDot p aa ha == 2 % p && ggDepANDot p aa X != 0 then
      wits.any fun w => ggTWNKillTest p N [(ha, aa)] R w
    else true

@[expose] def ggTWNTgt2 (p : Nat) (c2 : Option Nat) (c : Nat) : Nat :=
  match c2 with
  | none => 0
  | some c' => if c = c' then (p - 1) % p else 0

@[expose] def ggTWNCases2 (p N pos c : Nat) (c2 : Option Nat) (R : List (List Nat))
    (wits : List GGTWNKill) : Bool :=
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
              wits.any fun w => ggTWNKillTest p N [(h1, a1), (h2, a2)] R w
            else true
        else true
    else true

structure GGTWNData where
  one : List ((Nat × Nat × Nat × Nat) × List GGTWNKill)
  two : List ((Nat × Nat × Nat) × List GGTWNKill)

@[expose] def ggTWNCode : Option Nat → Nat
  | none => 0
  | some c' => c' + 1

@[expose] def ggTWNCheck (p N : Nat) (d : GGTWNData) : Bool :=
  ggTWNRootsOK p N (ggTWNRoots p N) &&
  d.one.all (fun e => e.2.all (ggTWNKillValid N N)) &&
  d.two.all (fun e => e.2.all (ggTWNKillValid N (N + 1))) &&
  [0, 1].all fun pos =>
    ((List.range (N - 1)).all fun c0 => [1, 2].all fun mi => [1, 2].all fun ni =>
      if ggTWNPat1B N pos c0 mi ni then
        match d.one.lookup (pos, c0, mi, ni) with
        | none => false
        | some wits => ggTWNCases1 p N pos c0 mi ni (ggTWNRoots p N) wits
      else true) &&
    ((List.range (N - 1)).all fun c => (none :: (List.range (N - 1)).map some).all fun c2 =>
      if ggTWNPat2B N pos c c2 then
        match d.two.lookup (pos, c, ggTWNCode c2) with
        | none => false
        | some wits => ggTWNCases2 p N pos c c2 (ggTWNRoots p N) wits
      else true)

@[expose] def twData77 : GGTWNData :=
  ⟨[
    ((0, 1, 1, 1), [
      GGTWNKill.tv ⟨0, [1], 0, [6, 5, 6, 1]⟩,
      GGTWNKill.tv ⟨0, [6, 5, 6, 1], 0, [1, 6, 5, 6, 1]⟩,
      GGTWNKill.line ⟨0, [6, 5, 6, 5, 0, 6], 1, []⟩,
      GGTWNKill.line ⟨5, [6, 1, 0, 6], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [6]⟩,
      GGTWNKill.line ⟨0, [6, 5, 1, 0, 6, 1], 0, []⟩,
      GGTWNKill.line ⟨5, [6, 5, 6, 5, 1, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 5, 1, 6], 0, []⟩,
      GGTWNKill.tv ⟨1, [], 2, [6, 5, 4, 3]⟩]),
    ((0, 1, 1, 2), [
      GGTWNKill.tv ⟨0, [1], 0, [6, 5, 6, 1]⟩,
      GGTWNKill.line ⟨6, [6, 5, 0, 1, 0], 0, []⟩,
      GGTWNKill.tv ⟨6, [], 6, [0]⟩,
      GGTWNKill.line ⟨3, [6, 0, 1, 6, 2, 1, 6, 5, 4], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 1, 6, 2, 0, 1], 0, []⟩,
      GGTWNKill.tv ⟨1, [], 1, [6, 0, 6]⟩,
      GGTWNKill.line ⟨6, [6, 1, 2, 0, 1], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 5, 1, 6, 5, 0], 0, []⟩]),
    ((0, 1, 2, 1), [
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.line ⟨6, [6, 5, 0, 1, 0], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 6, 1]⟩,
      GGTWNKill.line ⟨6, [6, 1, 6, 2, 0, 1], 0, []⟩,
      GGTWNKill.tv ⟨1, [6], 1, [0, 1, 6, 1, 0, 6]⟩,
      GGTWNKill.line ⟨6, [6, 0, 6, 5], 1, []⟩,
      GGTWNKill.line ⟨3, [6, 0, 1, 6, 2, 1, 6, 5, 4], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 5, 1, 6, 5, 0], 0, []⟩]),
    ((0, 2, 1, 1), [
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.line ⟨5, [6, 5, 6, 5, 2, 6], 1, []⟩,
      GGTWNKill.line ⟨0, [6, 5, 6, 5, 2, 6], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 2, 6, 2, 1]⟩,
      GGTWNKill.line ⟨0, [6, 0, 6, 2, 0, 6], 3, []⟩,
      GGTWNKill.line ⟨0, [6, 5, 4, 3, 2, 6], 0, []⟩,
      GGTWNKill.line ⟨1, [6, 2, 0, 6, 3, 2], 0, []⟩,
      GGTWNKill.line ⟨3, [6, 5, 2, 6, 5, 4], 1, []⟩,
      GGTWNKill.line ⟨0, [6, 2, 0, 6, 1], 0, []⟩]),
    ((0, 3, 1, 1), [
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.tv ⟨3, [], 3, [4, 5, 6, 5, 4]⟩,
      GGTWNKill.line ⟨5, [6, 5, 6, 5, 3, 6], 2, []⟩,
      GGTWNKill.line ⟨0, [6, 0, 6, 3, 0, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 5, 6, 5, 3, 6], 0, []⟩,
      GGTWNKill.line ⟨1, [6, 5, 0, 6, 3, 2], 0, []⟩,
      GGTWNKill.line ⟨2, [6, 5, 3, 6, 4, 3], 1, []⟩,
      GGTWNKill.line ⟨0, [6, 3, 0, 6, 2, 1], 0, []⟩,
      GGTWNKill.line ⟨4, [6, 3, 0, 6, 5], 0, []⟩]),
    ((0, 4, 1, 1), [
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.tv ⟨4, [6, 0, 6, 5], 4, [4, 6, 0, 6, 5]⟩,
      GGTWNKill.line ⟨4, [6, 0, 6, 5, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 4, 5, 6], 0, []⟩,
      GGTWNKill.tv ⟨5, [], 6, []⟩,
      GGTWNKill.line ⟨4, [6, 5, 4, 0, 6, 5], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 0, 6, 4, 0, 6], 1, []⟩,
      GGTWNKill.tv ⟨0, [], 1, [6, 4, 3, 2]⟩]),
    ((0, 4, 1, 2), [
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.line ⟨6, [6, 4, 5, 4, 0], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 4, 6, 0], 1, []⟩,
      GGTWNKill.line ⟨4, [6, 4, 3, 2, 1, 0, 6, 5], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 4, 6, 5, 3, 4], 2, []⟩,
      GGTWNKill.line ⟨6, [6, 4, 6, 3, 4, 5], 2, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [6, 5, 6]⟩,
      GGTWNKill.line ⟨4, [6, 5, 4, 6, 5], 3, []⟩,
      GGTWNKill.line ⟨6, [6, 5, 0, 6, 4, 0], 0, []⟩]),
    ((0, 4, 2, 1), [
      GGTWNKill.tv ⟨6, [], 6, [4, 5, 6, 5, 4]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6, 4, 6]⟩,
      GGTWNKill.line ⟨0, [6, 5, 4, 6], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [6]⟩,
      GGTWNKill.line ⟨6, [6, 4, 5, 4, 0], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 4, 6, 5, 3, 4], 2, []⟩,
      GGTWNKill.line ⟨6, [6, 4, 5, 3, 4], 2, []⟩,
      GGTWNKill.line ⟨4, [6, 5, 0, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 5, 4, 6, 3, 4, 6, 2, 1], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 5, 0, 6, 4, 0], 0, []⟩]),
    ((1, 0, 1, 1), [
      GGTWNKill.tv ⟨3, [5, 6, 4], 3, [4, 6, 4, 5, 6, 4]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [6, 5, 6]⟩,
      GGTWNKill.line ⟨0, [6, 5, 4, 6], 0, []⟩,
      GGTWNKill.line ⟨5, [6, 5, 6, 5, 0, 6], 1, []⟩,
      GGTWNKill.line ⟨4, [6, 4, 3, 2, 1, 0, 6, 5], 0, []⟩,
      GGTWNKill.line ⟨4, [4, 6, 5, 4, 6, 5], 3, []⟩,
      GGTWNKill.tv ⟨0, [3, 2, 1], 0, [6, 4, 6, 3, 2, 1]⟩,
      GGTWNKill.tv ⟨0, [], 1, [6, 5, 4, 3, 2]⟩,
      GGTWNKill.tv ⟨6, [], 6, [4]⟩,
      GGTWNKill.line ⟨4, [6, 5], 3, []⟩]),
    ((1, 0, 1, 2), [
      GGTWNKill.tv ⟨5, [], 5, [6, 4, 6]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.line ⟨5, [6, 0, 6, 5, 4, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 4, 6, 3, 2, 1], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 5, 3, 4], 4, []⟩,
      GGTWNKill.line ⟨6, [6, 5, 6, 4, 0], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 0, 6, 4], 1, []⟩,
      GGTWNKill.line ⟨6, [6, 4, 5, 1, 0, 6, 4, 5, 0], 0, []⟩]),
    ((1, 0, 2, 1), [
      GGTWNKill.tv ⟨5, [], 5, [6, 4, 6]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.line ⟨4, [6, 4, 6, 5], 3, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [6]⟩,
      GGTWNKill.line ⟨0, [6, 5, 4, 6], 0, []⟩,
      GGTWNKill.line ⟨4, [6, 4, 5, 0, 6], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 0, 6, 4], 1, []⟩,
      GGTWNKill.line ⟨4, [6, 5, 4, 0, 6, 5], 0, []⟩,
      GGTWNKill.line ⟨6, [6, 5, 0, 6, 5, 1, 0], 0, []⟩]),
    ((1, 1, 1, 1), [
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5, 6, 5]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨4, [6], 4, [5, 6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [6, 4, 5, 4, 6]⟩,
      GGTWNKill.line ⟨1, [6, 5, 6, 4, 6], 0, []⟩,
      GGTWNKill.line ⟨5, [6, 4, 5, 1, 6], 0, []⟩,
      GGTWNKill.tv ⟨6, [], 6, [4]⟩,
      GGTWNKill.line ⟨5, [6, 5, 6, 5, 1, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 4, 5, 3, 4, 2, 1, 6, 4, 3, 2, 1], 0, []⟩]),
    ((1, 2, 1, 1), [
      GGTWNKill.tv ⟨2, [], 2, [3, 4, 6, 4, 3]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6, 4, 5, 4, 6]⟩,
      GGTWNKill.line ⟨2, [6, 4, 6, 4, 3], 1, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [6]⟩,
      GGTWNKill.line ⟨2, [6, 5, 6, 4, 6, 3], 1, []⟩,
      GGTWNKill.line ⟨3, [6, 4, 2, 6, 4], 1, []⟩,
      GGTWNKill.line ⟨2, [6, 5, 4, 6], 1, []⟩,
      GGTWNKill.line ⟨3, [6, 5, 2, 6, 5, 4], 1, []⟩,
      GGTWNKill.line ⟨2, [6, 4, 5, 6, 4, 3], 1, []⟩,
      GGTWNKill.line ⟨2, [6, 4, 6, 5, 4, 6], 1, []⟩]),
    ((1, 3, 1, 1), [
      GGTWNKill.tv ⟨4, [], 4, [6]⟩,
      GGTWNKill.tv ⟨3, [], 3, [4, 6, 4, 6, 4]⟩,
      GGTWNKill.tv ⟨3, [], 3, [6, 4, 5, 4, 6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.tv ⟨3, [], 3, [6, 4, 6]⟩,
      GGTWNKill.line ⟨2, [6, 3, 4, 5, 6, 3], 1, []⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.line ⟨4, [6, 5, 3, 6, 5], 2, []⟩,
      GGTWNKill.line ⟨3, [6, 4, 6, 5, 4, 6], 2, []⟩,
      GGTWNKill.line ⟨4, [6, 5, 3, 6], 2, []⟩]),
    ((1, 3, 1, 2), [
      GGTWNKill.tv ⟨3, [], 3, [4, 6, 4]⟩,
      GGTWNKill.tv ⟨6, [], 6, [3, 4, 5, 4, 3]⟩,
      GGTWNKill.line ⟨6, [6, 3, 6, 4, 2, 3], 1, []⟩,
      GGTWNKill.line ⟨2, [6, 5, 3, 4, 6, 5, 4, 3], 1, []⟩,
      GGTWNKill.tv ⟨6, [], 6, [5]⟩,
      GGTWNKill.line ⟨6, [6, 5, 6, 3, 4, 5], 2, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [6]⟩,
      GGTWNKill.line ⟨4, [6, 3, 4, 5, 6], 2, []⟩]),
    ((1, 3, 2, 1), [
      GGTWNKill.tv ⟨4, [], 4, [6]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.line ⟨6, [6, 3, 6, 5], 2, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [6, 3, 6]⟩,
      GGTWNKill.line ⟨4, [6, 5, 6, 3, 6], 2, []⟩,
      GGTWNKill.line ⟨6, [6, 4, 6, 5, 3], 2, []⟩,
      GGTWNKill.line ⟨3, [6, 4], 2, []⟩,
      GGTWNKill.line ⟨5, [6, 3, 4, 6], 2, []⟩,
      GGTWNKill.line ⟨2, [6, 4, 5, 3, 4, 6, 3], 1, []⟩])
  ], [
    ((0, 1, 0), [
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.tv ⟨7, [], 7, [0]⟩,
      GGTWNKill.tv ⟨0, [], 0, [6, 7, 6]⟩,
      GGTWNKill.tv ⟨5, [], 5, [7, 6, 5, 6, 7]⟩,
      GGTWNKill.tv ⟨7, [], 6, [6, 5, 7]⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 6, 0, 6, 1]⟩,
      GGTWNKill.line ⟨6, [6, 5, 6, 7, 0], 1, []⟩,
      GGTWNKill.line ⟨7, [7, 5, 7, 0], 0, []⟩,
      GGTWNKill.tv ⟨1, [], 1, [6, 0, 7, 0, 6]⟩,
      GGTWNKill.tv ⟨2, [], 0, [3, 4, 5, 7, 1]⟩,
      GGTWNKill.line ⟨1, [6, 7, 5, 0, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 5, 7, 1], 0, []⟩,
      GGTWNKill.line ⟨5, [6, 7], 0, []⟩]),
    ((0, 1, 5), [
      GGTWNKill.tv ⟨5, [], 5, [7, 0, 7]⟩,
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.line ⟨0, [7, 6, 5, 4, 7], 0, []⟩,
      GGTWNKill.tv ⟨7, [], 7, [0, 6, 5, 6, 0]⟩,
      GGTWNKill.tv ⟨6, [7, 5], 6, [0, 7, 5]⟩,
      GGTWNKill.tv ⟨4, [], 4, [7, 5, 7]⟩,
      GGTWNKill.line ⟨6, [7, 4, 5, 0], 0, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [7, 5, 7, 5, 7]⟩,
      GGTWNKill.line ⟨1, [7, 5, 0, 6], 1, []⟩,
      GGTWNKill.line ⟨0, [7, 4, 5, 7], 0, []⟩,
      GGTWNKill.line ⟨0, [7, 0, 7, 6, 1], 0, []⟩,
      GGTWNKill.line ⟨0, [7, 5, 6], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 1, [7, 4, 3, 2]⟩]),
    ((0, 4, 0), [
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.tv ⟨7, [], 7, [0]⟩,
      GGTWNKill.tv ⟨6, [], 6, [7, 5, 7]⟩,
      GGTWNKill.tv ⟨0, [], 0, [6, 7, 6]⟩,
      GGTWNKill.tv ⟨0, [], 0, [6, 0, 7, 0, 6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5, 6, 5]⟩,
      GGTWNKill.line ⟨4, [6, 7, 5, 0, 6], 1, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [6, 5, 7, 5, 6]⟩,
      GGTWNKill.tv ⟨0, [], 1, [7, 5, 4, 3, 2]⟩,
      GGTWNKill.line ⟨7, [7, 5, 7, 0], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [7, 5, 6, 5, 7]⟩,
      GGTWNKill.line ⟨5, [7, 0, 6], 0, []⟩,
      GGTWNKill.line ⟨5, [7, 1, 0, 6, 7], 0, []⟩]),
    ((0, 4, 2), [
      GGTWNKill.tv ⟨5, [], 5, [7, 0, 7]⟩,
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 6]⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 7, 1]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.line ⟨0, [7, 6, 5, 4, 6], 0, []⟩,
      GGTWNKill.line ⟨4, [6, 5, 0, 6], 0, []⟩,
      GGTWNKill.line ⟨0, [6, 5, 0, 1, 7], 0, []⟩,
      GGTWNKill.line ⟨7, [6, 5], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 7, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [6, 5, 7, 5, 6]⟩,
      GGTWNKill.line ⟨0, [6, 4, 5, 7], 0, []⟩,
      GGTWNKill.line ⟨7, [6, 0], 0, []⟩,
      GGTWNKill.line ⟨0, [7, 6, 0, 6, 1], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 1, [6, 4, 3, 2]⟩]),
    ((1, 0, 0), [
      GGTWNKill.tv ⟨7, [], 7, [5]⟩,
      GGTWNKill.tv ⟨5, [], 5, [7, 6, 4, 6, 7]⟩,
      GGTWNKill.tv ⟨7, [], 7, [4, 6, 7, 6, 4]⟩,
      GGTWNKill.tv ⟨6, [], 6, [7, 4, 7]⟩,
      GGTWNKill.tv ⟨7, [6, 4], 7, [5, 6, 4]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.line ⟨0, [7, 6, 4, 6], 0, []⟩,
      GGTWNKill.line ⟨7, [6, 4], 0, []⟩,
      GGTWNKill.line ⟨4, [6, 5, 6], 3, []⟩,
      GGTWNKill.line ⟨7, [6, 4, 5, 4], 0, []⟩,
      GGTWNKill.tv ⟨7, [], 7, [5, 6, 5]⟩,
      GGTWNKill.line ⟨0, [6, 4, 7, 6], 1, []⟩,
      GGTWNKill.line ⟨6, [6, 7, 4], 0, []⟩,
      GGTWNKill.line ⟨4, [6, 7], 0, []⟩]),
    ((1, 0, 4), [
      GGTWNKill.tv ⟨4, [], 4, [5, 7, 4, 7, 5]⟩,
      GGTWNKill.line ⟨7, [7, 3, 4], 2, []⟩,
      GGTWNKill.tv ⟨5, [], 5, [6, 4, 7, 4, 6]⟩,
      GGTWNKill.line ⟨6, [7, 4, 5], 0, []⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.line ⟨2, [7, 3, 4, 5, 7, 3], 1, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 7, 5]⟩,
      GGTWNKill.line ⟨7, [6, 5, 4], 0, []⟩,
      GGTWNKill.line ⟨6, [7, 5, 4], 0, []⟩,
      GGTWNKill.line ⟨5, [6, 4, 5, 7], 0, []⟩,
      GGTWNKill.line ⟨6, [7, 4, 5, 3, 4], 0, []⟩,
      GGTWNKill.tv ⟨4, [], 7, []⟩]),
    ((1, 3, 0), [
      GGTWNKill.tv ⟨7, [], 7, [5]⟩,
      GGTWNKill.tv ⟨4, [], 4, [6]⟩,
      GGTWNKill.tv ⟨3, [], 3, [6, 4, 5, 4, 6]⟩,
      GGTWNKill.tv ⟨7, [], 6, [6, 4, 7]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.tv ⟨3, [], 3, [6, 4, 6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 7, 6, 5]⟩,
      GGTWNKill.line ⟨6, [7, 6, 3, 4, 7], 2, []⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.line ⟨7, [6, 5], 3, []⟩,
      GGTWNKill.line ⟨6, [7, 5], 3, []⟩,
      GGTWNKill.line ⟨2, [6, 3, 4, 7, 6, 3], 1, []⟩,
      GGTWNKill.line ⟨3, [6, 7, 4, 6, 4], 2, []⟩,
      GGTWNKill.line ⟨7, [6, 3, 4], 2, []⟩]),
    ((1, 3, 1), [
      GGTWNKill.line ⟨7, [6, 4, 5], 0, []⟩,
      GGTWNKill.tv ⟨4, [], 4, [6]⟩,
      GGTWNKill.tv ⟨5, [], 5, [6]⟩,
      GGTWNKill.tv ⟨4, [], 4, [5, 6, 5]⟩,
      GGTWNKill.tv ⟨3, [], 3, [6, 4, 6]⟩,
      GGTWNKill.line ⟨2, [6, 3, 4, 5, 6, 3], 1, []⟩,
      GGTWNKill.line ⟨0, [6, 4, 7, 4, 7], 0, []⟩,
      GGTWNKill.line ⟨7, [6, 5, 4], 0, []⟩,
      GGTWNKill.line ⟨6, [7, 5, 4], 0, []⟩,
      GGTWNKill.tv ⟨5, [], 5, [7]⟩,
      GGTWNKill.line ⟨3, [7, 6, 4], 0, []⟩])
  ]⟩

@[expose] def twData510 : GGTWNData :=
  ⟨[
    ((0, 1, 1, 1), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨1, [9], 1, [8, 0, 9, 8, 0, 9]⟩,
      GGTWNKill.line ⟨8, [9, 1, 2, 0, 1, 9], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 9, []⟩,
      GGTWNKill.line ⟨0, [9, 8, 1, 9, 2, 1], 1, []⟩,
      GGTWNKill.tv ⟨1, [2], 3, [9, 8, 7, 6, 5, 4]⟩]),
    ((0, 1, 1, 2), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨0, [], 0, [9, 1, 9]⟩,
      GGTWNKill.line ⟨9, [9, 8, 9, 7, 8, 1], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 9, 1]⟩,
      GGTWNKill.line ⟨9, [9, 1, 0], 2, []⟩]),
    ((0, 1, 2, 1), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨0, [], 0, [9, 1, 9]⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 9, 1]⟩,
      GGTWNKill.line ⟨9, [9, 8, 9, 7, 8, 1], 0, []⟩,
      GGTWNKill.line ⟨9, [9, 1, 0], 2, []⟩]),
    ((0, 2, 1, 1), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.line ⟨0, [9, 8, 0, 9], 0, []⟩,
      GGTWNKill.line ⟨2, [9, 8, 9, 0, 9], 0, []⟩,
      GGTWNKill.line ⟨1, [9, 8, 2, 9, 3, 2], 0, []⟩,
      GGTWNKill.line ⟨0, [9, 2, 3, 1, 2, 9], 0, []⟩,
      GGTWNKill.line ⟨0, [9, 8, 2, 0, 9, 3, 2, 1], 0, []⟩]),
    ((0, 3, 1, 1), [
      GGTWNKill.tv ⟨8, [], 8, [9]⟩,
      GGTWNKill.line ⟨0, [9, 8, 3, 9, 7, 8, 2, 3, 4, 1, 2, 3, 9, 5, 4, 3, 2, 1], 2, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [0]⟩,
      GGTWNKill.line ⟨3, [9, 8, 9, 0, 9], 0, []⟩,
      GGTWNKill.line ⟨0, [9, 3, 2, 1], 0, []⟩,
      GGTWNKill.tv ⟨0, [2, 3, 9, 4, 3, 2, 1], 0, [1, 0, 9, 3, 4, 2, 3, 9, 1]⟩,
      GGTWNKill.line ⟨0, [9, 8, 3, 9], 0, []⟩]),
    ((0, 5, 1, 1), [
      GGTWNKill.line ⟨0, [9, 5, 0, 9, 6, 7, 8, 5, 6, 7, 4, 5, 6, 3, 4, 5, 9, 1], 1, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨5, [8, 0, 9, 7, 6], 5, [9, 8, 0, 9, 7, 6]⟩,
      GGTWNKill.line ⟨0, [9, 8, 5, 9], 0, []⟩,
      GGTWNKill.line ⟨5, [9, 8, 0, 9], 0, []⟩,
      GGTWNKill.line ⟨9, [9, 8, 0], 1, []⟩,
      GGTWNKill.tv ⟨4, [6, 5, 9, 8, 7, 6, 5], 4, [7, 8, 9, 5, 6, 7, 8, 9, 5]⟩]),
    ((0, 6, 1, 1), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨6, [], 6, [7, 8, 9, 8, 7]⟩,
      GGTWNKill.line ⟨7, [9, 6, 7, 8, 9, 8], 5, []⟩,
      GGTWNKill.line ⟨5, [9, 6, 0, 9, 7, 6], 0, []⟩,
      GGTWNKill.line ⟨6, [9, 8, 9, 7, 8, 9], 5, []⟩,
      GGTWNKill.line ⟨0, [9, 6, 7, 8, 7, 5, 6, 9], 0, []⟩]),
    ((0, 7, 1, 1), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨7, [], 7, [8, 9, 8]⟩,
      GGTWNKill.line ⟨9, [9, 0, 9, 8, 1, 0], 1, []⟩,
      GGTWNKill.line ⟨0, [9, 7, 8, 6, 7, 9], 0, []⟩,
      GGTWNKill.tv ⟨8, [], 9, []⟩,
      GGTWNKill.line ⟨6, [9, 7, 0, 9, 8, 7], 0, []⟩,
      GGTWNKill.tv ⟨0, [1], 2, [9, 7, 6, 5, 4, 3]⟩]),
    ((0, 7, 1, 2), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨7, [], 7, [8, 9, 8]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9, 7, 9]⟩,
      GGTWNKill.line ⟨9, [9, 8, 7], 6, []⟩,
      GGTWNKill.line ⟨9, [9, 0, 9, 7, 1, 0], 1, []⟩]),
    ((0, 7, 2, 1), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9, 7, 9]⟩,
      GGTWNKill.tv ⟨7, [], 7, [8, 9, 8]⟩,
      GGTWNKill.line ⟨9, [9, 8, 7], 6, []⟩,
      GGTWNKill.line ⟨9, [9, 8, 7, 9, 7, 0], 1, []⟩]),
    ((1, 0, 1, 1), [
      GGTWNKill.tv ⟨9, [], 9, [7, 8, 9, 8, 7]⟩,
      GGTWNKill.line ⟨0, [9, 7, 8, 6, 7, 9], 0, []⟩,
      GGTWNKill.line ⟨6, [9, 7, 0, 9, 8, 7], 0, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [8]⟩,
      GGTWNKill.tv ⟨0, [2, 1], 3, [9, 8, 7, 6, 5, 4]⟩,
      GGTWNKill.tv ⟨0, [1], 2, [9, 7, 6, 5, 4, 3]⟩]),
    ((1, 0, 1, 2), [
      GGTWNKill.line ⟨9, [9, 8, 7, 0], 0, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [7]⟩,
      GGTWNKill.line ⟨9, [9, 0, 9, 8, 1, 0], 1, []⟩,
      GGTWNKill.line ⟨9, [9, 7, 8, 6, 7], 5, []⟩,
      GGTWNKill.tv ⟨9, [8], 9, [7, 8]⟩]),
    ((1, 0, 2, 1), [
      GGTWNKill.line ⟨9, [9, 8, 7, 0], 0, []⟩,
      GGTWNKill.line ⟨9, [9, 7, 8, 6, 7], 5, []⟩,
      GGTWNKill.tv ⟨7, [], 7, [9]⟩,
      GGTWNKill.line ⟨9, [9, 7, 8, 0], 0, []⟩,
      GGTWNKill.line ⟨9, [9, 0, 9, 8, 1, 0], 1, []⟩,
      GGTWNKill.tv ⟨8, [], 8, [9]⟩]),
    ((1, 1, 1, 1), [
      GGTWNKill.line ⟨6, [9, 7, 8, 9, 7], 5, []⟩,
      GGTWNKill.line ⟨6, [9, 8, 7, 9, 8, 7], 5, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [7]⟩,
      GGTWNKill.line ⟨0, [9, 8, 1, 9, 2, 1], 1, []⟩,
      GGTWNKill.line ⟨0, [9, 7, 8, 6, 7, 1, 9, 7, 6, 5, 4, 3, 2, 1], 0, []⟩,
      GGTWNKill.line ⟨7, [9, 8], 6, []⟩]),
    ((1, 2, 1, 1), [
      GGTWNKill.line ⟨0, [9, 7, 8, 6, 7, 9, 2, 3, 1, 2, 9, 4, 3, 2, 1], 2, []⟩,
      GGTWNKill.line ⟨1, [9, 8, 2, 9, 3, 2], 0, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [7]⟩,
      GGTWNKill.tv ⟨7, [], 7, [8, 9, 8]⟩,
      GGTWNKill.line ⟨2, [9, 7, 8, 6, 7, 9], 1, []⟩]),
    ((1, 4, 1, 1), [
      GGTWNKill.line ⟨8, [9, 8, 7, 4, 9], 3, []⟩,
      GGTWNKill.tv ⟨7, [], 7, [9]⟩,
      GGTWNKill.line ⟨9, [9, 7, 9, 7, 8, 7], 6, []⟩,
      GGTWNKill.line ⟨7, [9, 8, 4, 9], 3, []⟩,
      GGTWNKill.line ⟨0, [9, 4, 5, 3, 4, 9, 6, 7, 5, 6, 2, 3, 4, 5, 1, 2, 3, 4, 9, 8, 7, 6, 5, 4,
        3, 2, 1], 2, []⟩]),
    ((1, 5, 1, 1), [
      GGTWNKill.tv ⟨9, [], 9, [7, 8, 9, 8, 7]⟩,
      GGTWNKill.line ⟨4, [9, 8, 5, 9, 6, 5], 3, []⟩,
      GGTWNKill.line ⟨6, [9, 5, 6, 7, 9, 7], 4, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [8]⟩,
      GGTWNKill.tv ⟨4, [6, 5, 9, 8, 7, 6, 5], 4, [7, 8, 9, 5, 6, 7, 8, 9, 5]⟩,
      GGTWNKill.line ⟨4, [9, 7, 6, 5, 9, 7, 6, 5], 3, []⟩]),
    ((1, 6, 1, 1), [
      GGTWNKill.tv ⟨7, [], 7, [9]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9]⟩,
      GGTWNKill.tv ⟨7, [], 7, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨6, [], 6, [9, 7, 9]⟩,
      GGTWNKill.line ⟨6, [9, 8, 9, 7, 8, 9], 5, []⟩,
      GGTWNKill.line ⟨5, [9, 7, 6, 9, 7, 6], 4, []⟩,
      GGTWNKill.line ⟨6, [9, 7, 9, 8, 9], 5, []⟩]),
    ((1, 6, 1, 2), [
      GGTWNKill.tv ⟨7, [], 7, [9]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9]⟩,
      GGTWNKill.tv ⟨7, [9], 7, [8, 9]⟩,
      GGTWNKill.line ⟨9, [9, 7, 6], 5, []⟩,
      GGTWNKill.line ⟨9, [9, 8, 7], 6, []⟩,
      GGTWNKill.tv ⟨7, [], 8, [8, 9]⟩]),
    ((1, 6, 2, 1), [
      GGTWNKill.tv ⟨7, [], 7, [9]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9]⟩,
      GGTWNKill.line ⟨9, [9, 8, 7], 6, []⟩,
      GGTWNKill.tv ⟨7, [9], 7, [8, 9]⟩,
      GGTWNKill.line ⟨9, [9, 7, 6, 9, 8], 5, []⟩])
  ], [
    ((0, 1, 0), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨10, [], 10, [0]⟩,
      GGTWNKill.tv ⟨0, [], 0, [9, 10, 9]⟩,
      GGTWNKill.tv ⟨9, [], 9, [8, 10, 8]⟩,
      GGTWNKill.line ⟨1, [9, 10, 8, 0, 9], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 9, 1]⟩,
      GGTWNKill.tv ⟨0, [], 9, []⟩,
      GGTWNKill.line ⟨8, [9, 10], 0, []⟩]),
    ((0, 1, 8), [
      GGTWNKill.tv ⟨8, [], 8, [10, 0, 10]⟩,
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨9, [], 10, [8, 10, 8, 0]⟩,
      GGTWNKill.tv ⟨7, [], 7, [10, 8, 10]⟩,
      GGTWNKill.line ⟨0, [10, 7, 8, 0, 9, 1], 0, []⟩,
      GGTWNKill.tv ⟨0, [], 9, [10, 8]⟩,
      GGTWNKill.line ⟨0, [9, 1, 0, 10], 0, []⟩,
      GGTWNKill.line ⟨0, [9, 8, 1, 9], 0, []⟩,
      GGTWNKill.tv ⟨0, [1], 2, [10, 7, 6, 5, 4, 3]⟩]),
    ((0, 7, 0), [
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨10, [], 10, [0]⟩,
      GGTWNKill.tv ⟨7, [], 7, [8, 9, 8]⟩,
      GGTWNKill.tv ⟨9, [], 9, [0, 10, 0]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9, 10, 9]⟩,
      GGTWNKill.line ⟨7, [9, 10, 8, 1, 0, 9], 0, []⟩,
      GGTWNKill.tv ⟨8, [], 9, []⟩,
      GGTWNKill.line ⟨0, [9, 10], 1, []⟩]),
    ((0, 7, 2), [
      GGTWNKill.tv ⟨8, [], 8, [10, 0, 10]⟩,
      GGTWNKill.tv ⟨0, [], 0, [9, 8, 9]⟩,
      GGTWNKill.tv ⟨0, [], 0, [1, 10, 1]⟩,
      GGTWNKill.line ⟨7, [10, 8, 0, 9], 6, []⟩,
      GGTWNKill.line ⟨9, [10, 0], 0, []⟩,
      GGTWNKill.tv ⟨8, [], 9, [10, 0, 10, 0]⟩,
      GGTWNKill.line ⟨0, [10, 8, 10, 7, 9, 1], 0, []⟩,
      GGTWNKill.tv ⟨0, [1], 2, [9, 7, 6, 5, 4, 3]⟩]),
    ((1, 0, 0), [
      GGTWNKill.tv ⟨10, [], 10, [8]⟩,
      GGTWNKill.line ⟨9, [9, 7, 8, 10], 0, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [8, 7, 9, 7, 8]⟩,
      GGTWNKill.line ⟨0, [9, 8, 10, 9], 1, []⟩,
      GGTWNKill.line ⟨7, [9, 10, 0, 9], 1, []⟩,
      GGTWNKill.tv ⟨9, [], 9, [8]⟩,
      GGTWNKill.tv ⟨8, [], 8, [10, 8, 9, 8, 10]⟩,
      GGTWNKill.line ⟨8, [10, 9], 0, []⟩]),
    ((1, 0, 7), [
      GGTWNKill.line ⟨9, [10, 8, 7], 0, []⟩,
      GGTWNKill.tv ⟨8, [], 8, [10]⟩,
      GGTWNKill.tv ⟨9, [], 9, [8, 7, 9, 7, 8]⟩,
      GGTWNKill.tv ⟨9, [], 9, [7, 10, 7]⟩,
      GGTWNKill.line ⟨9, [10, 8], 0, []⟩,
      GGTWNKill.line ⟨5, [10, 7, 6, 10, 7, 6], 4, []⟩,
      GGTWNKill.line ⟨6, [10, 7, 10], 5, []⟩,
      GGTWNKill.tv ⟨0, [7, 8, 9], 7, [0, 9, 8, 10]⟩]),
    ((1, 6, 0), [
      GGTWNKill.tv ⟨10, [], 10, [8]⟩,
      GGTWNKill.tv ⟨7, [], 7, [9]⟩,
      GGTWNKill.tv ⟨6, [], 6, [9, 7, 8, 7, 9]⟩,
      GGTWNKill.tv ⟨7, [], 7, [8, 9, 8]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9]⟩,
      GGTWNKill.line ⟨6, [9, 8, 10, 9], 5, []⟩,
      GGTWNKill.line ⟨5, [9, 7, 6, 9, 7, 6], 4, []⟩]),
    ((1, 6, 1), [
      GGTWNKill.line ⟨9, [10, 8, 7], 0, []⟩,
      GGTWNKill.tv ⟨7, [], 7, [9]⟩,
      GGTWNKill.tv ⟨8, [], 8, [9]⟩,
      GGTWNKill.line ⟨9, [10, 7, 8], 0, []⟩,
      GGTWNKill.line ⟨10, [9, 8, 7], 0, []⟩,
      GGTWNKill.tv ⟨7, [], 8, [9]⟩,
      GGTWNKill.tv ⟨10, [], 10, [8]⟩,
      GGTWNKill.line ⟨10, [9, 8], 0, []⟩,
      GGTWNKill.line ⟨6, [10, 9, 7], 0, []⟩])
  ]⟩

end Certificates.TwoDepSmall
