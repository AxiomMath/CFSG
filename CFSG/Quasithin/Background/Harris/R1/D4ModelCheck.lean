module

public import CFSG.Quasithin.Background.Harris.R1.D4Q2Check
public import Certificates.Data.D4HexLinkCheck
public meta import CFSG.Quasithin.Background.Harris.R1.D4Q2Check
public meta import Certificates.Data.D4HexLinkCheck

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

@[expose] def ptArr (w : List ℕ) : Array ℕ :=
  w.foldr (fun k acc => compA 819 CFSG.D4Hex.permArrs[k]! acc) (idA 819)

@[expose] def fixLine (w : List ℕ) : Bool := CFSG.D4Hex.fixesLine0 (ptArr w)

@[expose] def fixPt (w : List ℕ) : Bool := (ptArr w)[0]! == 0

@[expose] def movePt (w : List ℕ) : Bool := !((ptArr w)[0]! == 0)

@[expose] def x0A : Array ℕ := wordR d4Gens (hWords.getD 1 [])

@[expose] def x0IsVB : Bool := x0A == (mkClass d4Gens z0R).T[1]!

@[expose] def zetaConjOK : Bool :=
  [(0, [2]), (1, [0, 1]), (2, [1, 2]), (6, [0, 2, 6, 0, 2])].all fun p =>
    mulR zA d4Gens[p.1]! == mulR (wordR d4Gens p.2) zA

@[expose] def vCommOK : Bool :=
  qGensA.all fun g => mulR g z0R == mulR z0R g && mulR g x0A == mulR x0A g

@[expose] def r0NotComm : Bool := !(mulR r0A x0A == mulR x0A r0A)

@[expose] def centerCheck (T : Array (Array ℕ)) : Bool :=
  allLt T.size fun i =>
    !(qGensA.all fun g => mulR T[i]! g == mulR g T[i]!) || T[i]! == oneR || T[i]! == z0R ||
      T[i]! == x0A || T[i]! == mulR z0R x0A

@[expose] def kcCheck (TK : Array (Array ℕ)) : Bool :=
  allLt TK.size fun j =>
    !(qGensA.all fun g => mulR TK[j]! g == mulR g TK[j]!) || TK[j]! == oneR

@[expose] def bfsPl (gs : Array (Array ℕ)) : List (ℕ × ℕ) := Id.run do
  let mut seen : Std.HashMap (Array ℕ) Unit := {}
  seen := seen.insert oneR ()
  let mut T : Array (Array ℕ) := #[oneR]
  let mut pl : Array (ℕ × ℕ) := #[]
  let mut i := 0
  while i < T.size do
    let y := T[i]!
    for k in [0:gs.size] do
      let c := mulR y gs[k]!
      if !seen.contains c then
        seen := seen.insert c ()
        T := T.push c
        pl := pl.push (i, k)
    i := i + 1
  return pl.toList

@[expose] def bGens : Array (Array ℕ) := #[y1A, y2A, zA, r0A]

@[expose] def bGensInv : Array (Array ℕ) := #[y1iA, y2A, zPowA[6]!, r0A]

@[expose] def bTabOK : Bool := tabOK bGens bGensInv (bfsPl bGens) 28672

@[expose] def cmA (q qi : Array ℕ) : Array ℕ := mulR (mulR q s0A) (mulR qi s0iA)

@[expose] def cmiA (q qi : Array ℕ) : Array ℕ := mulR (mulR s0A q) (mulR s0iA qi)

@[expose] def sGensA : Array (Array ℕ) := phiArr (cmA y1A y1iA) (cmA y2A y2A)

@[expose] def sGensInvA : Array (Array ℕ) := phiArr (cmiA y1A y1iA) (cmiA y2A y2A)

@[expose] def sInQ2 : Bool :=
  let idx := lookup (mkIdx tQ)
  sGensA.all (memR tQ idx)

@[expose] def sTabOK : Bool := tabOK sGensA sGensInvA (bfsPl sGensA) 2048

end CFSG.Quasithin.Background.Harris.R1.D4Vert
