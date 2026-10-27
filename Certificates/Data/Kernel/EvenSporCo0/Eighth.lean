module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypEighthInputs
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.Certificates.Kernel.Lie.CT.Core
public import Certificates.Data.Kernel.MonsterB.BfsReplay

public section

namespace CFSG.KC.EvenSporCo0

open CFSG.KC.Enum CFSG.KS CFSG.KLie.CT CFSG.Monster.Code CFSG.EvenSporadicStandard.TwoCo1

@[expose] noncomputable def sigRecP (p w : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sigRecP p w n ^^^ (if w.testBit (pg 5 (mask 5) p n) then 2 ^ n else 0)

@[expose] noncomputable def powSumP (p w : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => w ^^^ sigRecP p (powSumP p w k) 24

@[expose] noncomputable def imsP (p : ℕ) : List ℕ :=
  (List.range 12).map fun i => powSumP p (Bmask i) 8

@[expose] def xorSub (m : ℕ → ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => xorSub m s k ^^^ (if s.testBit k then m k else 0)

@[expose] def treeSumW (F : ℕ → ℕ) (m : ℕ → ℕ) (W : ℕ → Option ℕ) : ℕ → ℕ → ℕ
  | 0, a => F a
  | k + 1, a =>
    match W k with
    | some _ => 2 * treeSumW F m W k a
    | none => treeSumW F m W k a + treeSumW F m W k (a ^^^ m k)

@[expose] def witsOK (m : ℕ → ℕ) (W : ℕ → Option ℕ) (n : ℕ) : Bool :=
  (List.range n).all fun k =>
    match W k with
    | some s => m k == xorSub m s k
    | none => true

@[expose] def reduceB : List (ℕ × ℕ) → ℕ → ℕ → ℕ × ℕ
  | [], v, s => (v, s)
  | (b, t) :: B, v, s =>
    if v ^^^ b < v then reduceB B (v ^^^ b) (s ^^^ t) else reduceB B v s

@[expose] def insDesc (x : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [x]
  | y :: B => if y.1 < x.1 then x :: y :: B else y :: insDesc x B

@[expose] def witsGo : List (ℕ × ℕ) → ℕ → List ℕ → List (Option ℕ)
  | _, _, [] => []
  | B, k, v :: vs =>
    let r := reduceB B v 0
    if r.1 = 0 then some r.2 :: witsGo B (k + 1) vs
    else none :: witsGo (insDesc (r.1, r.2 ^^^ 2 ^ k) B) (k + 1) vs

@[expose] def wtF (x : ℕ) : ℕ :=
  badWt (CFSG.Monster.Code.popc 12 (x % 4096) + CFSG.Monster.Code.popc 12 (x / 4096 % 4096))

@[expose] noncomputable def eighthBadP (p : ℕ) : ℕ :=
  let ims := imsP p
  let ws := witsGo [] 0 ims
  if witsOK (fun i => ims.getD i 0) (fun k => ws.getD k none) 12 then
    treeSumW wtF (fun i => ims.getD i 0) (fun k => ws.getD k none) 12 0
  else 1

@[expose] noncomputable def pow8P (p : ℕ) : Bool :=
  let p2 := pcomp 24 5 (mask 5) p p
  let p4 := pcomp 24 5 (mask 5) p2 p2
  Nat.beq (pcomp 24 5 (mask 5) p4 p4) (pidn 24 5)

@[expose] noncomputable def eighthOKP (p : ℕ) : Bool := pow8P p && Nat.beq (eighthBadP p) 0

@[expose] noncomputable def edgesK (ng N : ℕ) (G T E : ℕ → ℕ) : Bool :=
  (List.range N).all fun i => (List.range ng).all fun k =>
    decide (fget (E i) k 16 < N) &&
      Nat.beq (T (fget (E i) k 16)) (pcomp 24 5 (mask 5) (G k) (T i))

@[expose] noncomputable def replayK (ng N : ℕ) (E : ℕ → ℕ) : Bool :=
  CFSG.KC.Bfs.replayOK (fun i k => fget (E i) k 16) ng N

@[expose] noncomputable def eighthBlk (T : ℕ → ℕ) (lo len : ℕ) : Bool :=
  (List.range len).all fun i => eighthOKP (T (lo + i))

end CFSG.KC.EvenSporCo0
