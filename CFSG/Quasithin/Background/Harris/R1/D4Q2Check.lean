module

public import CFSG.LargeExtraspecial.S63CD4Inputs
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords
public meta import CFSG.LargeExtraspecial.S63CD4Inputs
public meta import CFSG.Quasithin.Background.Harris.R1.D4VertWords

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

@[expose] def wA (i : ℕ) : Array ℕ := wordR d4Gens (nWords.getD i [])

@[expose] def y1A : Array ℕ := wA 0

@[expose] def y2A : Array ℕ := wA 1

@[expose] def zA : Array ℕ := wA 2

@[expose] def r0A : Array ℕ := wA 3

@[expose] def s0A : Array ℕ := wA 4

@[expose] def y1iA : Array ℕ := powRows 24 y1A 3

@[expose] def s0iA : Array ℕ := mulR s0A s0A

@[expose] def zPowA : Array (Array ℕ) := Array.ofFn (n := 8) fun i => powRows 24 zA i.val

@[expose] def cjA (i : ℕ) (x : Array ℕ) : Array ℕ := mulR (mulR zPowA[i]! x) zPowA[7 - i]!

@[expose] def phiArr (u v : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 14) fun j => if j.val < 7 then cjA j.val u else cjA (j.val - 7) v

@[expose] def relValR (f fi : Array (Array ℕ)) (r : List (Fin 14 × Bool)) : Array ℕ :=
  r.foldr (fun p acc => mulR (if p.2 then f[p.1.val]! else fi[p.1.val]!) acc) oneR

@[expose] def relsOK (f fi : Array (Array ℕ)) (rels : List (List (Fin 14 × Bool))) : Bool :=
  rels.all fun r => relValR f fi r == oneR

@[expose] def buildTabR (gs : Array (Array ℕ)) (pl : List (ℕ × ℕ)) : Array (Array ℕ) :=
  pl.foldl (fun acc pr => acc.push (mulR (acc.getD pr.1 oneR) (gs.getD pr.2 oneR))) #[oneR]

@[expose] def tabOKOn (gs gi T : Array (Array ℕ)) (idx : Array ℕ → ℕ) (N : ℕ) : Bool :=
  T.size == N && allLt T.size (fun i => idx T[i]! == i) &&
  allLt gs.size (fun i => mulR gs[i]! gi[i]! == oneR) &&
  allLt T.size fun j => allLt gs.size fun i =>
    memR T idx (mulR T[j]! gs[i]!) && memR T idx (mulR T[j]! gi[i]!)

@[expose] def tabOKWith (gs gi T : Array (Array ℕ)) (N : ℕ) : Bool :=
  tabOKOn gs gi T (lookup (mkIdx T)) N

@[expose] def tabOK (gs gi : Array (Array ℕ)) (pl : List (ℕ × ℕ)) (N : ℕ) : Bool :=
  tabOKWith gs gi (buildTabR gs pl) N

@[expose] def invOKT (T : Array (Array ℕ)) : Bool :=
  allLt T.size fun i => validR (invPow T[i]!) && mulR T[i]! (invPow T[i]!) == oneR

@[expose] def qGensA : Array (Array ℕ) := phiArr y1A y2A

@[expose] def qGensInvA : Array (Array ℕ) := phiArr y1iA y2A

@[expose] def tQ : Array (Array ℕ) := buildTabR qGensA tabQ2

@[expose] def kGens : Array (Array ℕ) := #[zA, r0A, s0A]

@[expose] def kGensInv : Array (Array ℕ) := #[zPowA[6]!, r0A, s0iA]

@[expose] def tK : Array (Array ℕ) := buildTabR kGens tabKc

@[expose] def pr1 (x : Array ℕ) : Bool :=
  !(mulR x x == oneR) && relsOK (phiArr x oneR) (phiArr (invPow x) oneR) qR1

@[expose] def pr2 (y : Array ℕ) : Bool :=
  relsOK (phiArr oneR y) (phiArr oneR (invPow y)) qR2

@[expose] def pairOK (TK : Array (Array ℕ)) (x y : Array ℕ) : Bool :=
  !relsOK (phiArr x y) (phiArr (invPow x) (invPow y)) qR12 ||
    TK.any fun k => mulR x k == mulR k y1A && mulR y k == mulR k y2A

@[expose] def pairCheck (T TK : Array (Array ℕ)) : Bool :=
  let B := T.filter pr2
  (T.filter pr1).all fun x => B.all fun y => pairOK TK x y

@[expose] def commCheck (TK : Array (Array ℕ)) : Bool :=
  allLt TK.size fun j => mulR TK[j]! zA == mulR zA TK[j]!

@[expose] def cubeCheck (TK : Array (Array ℕ)) : Bool :=
  allLt TK.size fun j =>
    !(mulR (mulR TK[j]! TK[j]!) TK[j]! == oneR) || TK[j]! == oneR || TK[j]! == s0A ||
      TK[j]! == s0iA

end CFSG.Quasithin.Background.Harris.R1.D4Vert
