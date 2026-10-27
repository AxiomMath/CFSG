module

public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three

public section

namespace CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native

set_option compiler.extract_closed false

@[expose] def frG1 : List Nat :=
  [25, 16, 25, 17, 13, 14, 24, 12, 16, 11, 20, 13, 10, 9, 4, 17, 6, 12, 8, 0, 22, 0, 19]

@[expose] def frH0 : List Nat :=
  [19, 21, 19, 14, 13, 14, 18, 23, 15, 23, 8, 10, 18, 11, 8, 22, 6, 6, 20, 7, 25, 0, 9, 17, 20]

@[expose] def frWc0 : List Nat := [21, 16, 8, 1]

@[expose] def frWc1 : List Nat := [20, 13, 1]

@[expose] def frEps : List (List Nat) := [
  [24, 19, 21, 19, 15, 24, 17, 13, 14, 14, 10, 21, 14, 20, 13],
  [25, 23, 17, 25, 12, 14, 16, 24, 14, 10, 15, 25, 12, 20],
  [16, 21, 18, 20, 12, 15, 19, 20, 15, 18, 10, 10, 19, 20, 14],
  [24, 17, 24, 15, 23, 19, 14, 22, 9, 9, 18, 15, 18],
  [25, 20, 19, 12, 14, 14, 14, 23, 13, 19, 8, 12, 17, 10, 24],
  [24, 20, 22, 20, 12, 17, 13, 14, 24, 17, 8, 8, 16, 18, 25]]

@[expose] def frOrbitSize : Nat := 3499200

@[expose] def frPt (c : Ctx) (w : List Nat) : Nat := ap (wordTab c w) 0

@[expose] def frS (c : Ctx) : Table := compT nPts (clsTab c 0) (clsTab c 305530)

@[expose] def frU (c : Ctx) (c0 c1 : Nat) : Table := compT nPts (clsTab c c0) (clsTab c c1)

@[expose] def frX (c : Ctx) (c0 c1 : Nat) : Table := compT nPts (frS c) (frU c c0 c1)

@[expose] def frLam (c : Ctx) (c0 c1 : Nat) : List Nat :=
  [0, 305530, clsPt c 0 305530, c0, c1, clsPt c c0 c1]

@[expose] def frWordsOK (c : Ctx) : Bool :=
  ([frG1, frH0, frWc0, frWc1] ++ frEps).all fun w => w.all fun l => decide (l < c.L.size)

@[expose] def frRelTab (E Ei : Array Table) (r : List (Fin 6 × Bool)) : Table :=
  r.foldl (fun acc x => compT nPts acc (if x.2 then E[x.1.val]! else Ei[x.1.val]!)) (idT nPts)

@[expose] def frFixes (T : Table) (c0 c1 : Nat) : Bool :=
  ap T 0 == 0 && ap T 305530 == 305530 && ap T c0 == c0 && ap T c1 == c1

@[expose] def frMoves (T : Table) : Bool := !(allIn 0 nPts fun i => ap T i == i)

@[expose] def frFrameOK (rels : List (List (Fin 6 × Bool))) (c : Ctx) : Bool :=
  let c0 := frPt c frWc0
  let c1 := frPt c frWc1
  let xT := frX c c0 c1
  let Tg := wordTab c frG1
  let E : Array Table := (frEps.map (wordTab c)).toArray
  let Ei : Array Table := E.map (invT nPts)
  frWordsOK c && !commB c 0 305530 && !commB c c0 c1 &&
    commB c 0 c0 && commB c 0 c1 && commB c 305530 c0 && commB c 305530 c1 &&
    [c0, c1, clsPt c c0 c1].all (fun a => a != 0 && a != 305530 && a != clsPt c 0 305530) &&
    compT nPts Tg (wordTab c [2]) == compT nPts xT Tg &&
    E.size == 6 && allIn 0 6 (fun i => invOK nPts E[i]! Ei[i]! && frFixes E[i]! c0 c1) &&
    frMoves E[0]! && rels.all (fun r => frRelTab E Ei r == idT nPts)

@[expose] def frPpB (c : Ctx) (xT : Table) (a : Nat) : Bool :=
  !commB c a (ap xT a) && ap xT (ap xT a) == clsPt c a (ap xT a)

@[expose] def frPA (c : Ctx) (xT : Table) : Array Nat := (Array.range nPts).filter (frPpB c xT)

@[expose] def frFail (c : Ctx) (xT : Table) (PA : Array Nat) (a : Nat) : Bool :=
  PA.any fun q => q != a && commB c a q && !commB c (ap xT a) q

@[expose] def frScanOK (c : Ctx) : Bool :=
  let c0 := frPt c frWc0
  let c1 := frPt c frWc1
  let xT := frX c c0 c1
  let PA := frPA c xT
  let lam := frLam c c0 c1
  lam.all (fun a => frPpB c xT a && !frFail c xT PA a) &&
    PA.all (fun a => lam.contains a || frFail c xT PA a)

@[expose] def frF (c : Ctx) : Array Nat :=
  (Array.range nPts).filter fun a => commB c 0 a && commB c 305530 a

@[expose] def frPos (F : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate nPts 0
  for i in [0:F.size] do
    r := r.set! F[i]! i
  return r

@[inline, expose] def frAct (L : Table) (F posF : Array Nat) (m k : Nat) : Nat :=
  posF[ap L F[k / m]!]! * m + posF[ap L F[k % m]!]!

@[expose] def frBfs (Ls : Array Table) (lv : Array Nat) (F posF : Array Nat) (root : Nat) :
    Tree := Id.run do
  let m := F.size
  let mut pos : Table := Array.replicate (m * m) none32
  let mut pts : Table := #[UInt32.ofNat root]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  pos := pos.set! root 0
  for h in [0:m * m] do
    if h < pts.size then
      let k := ap pts h
      for l in lv do
        let q := frAct Ls[l]! F posF m k
        if pos[q]! == none32 then
          pos := pos.set! q (UInt32.ofNat pts.size)
          pts := pts.push (UInt32.ofNat q)
          par := par.push (UInt32.ofNat h)
          lab := lab.push (UInt32.ofNat l)
    else break
  return ⟨pts, pos, par, lab⟩

@[inline, expose] def frAt (Ls : Array Table) (lv : Array Nat) (F posF : Array Nat) (m : Nat)
    (T : Tree) (k : Nat) : Bool :=
  let p := ap T.pts k
  decide (p < m * m) && ap T.pos p == k &&
    lv.all (fun l =>
      let L := Ls[l]!
      let q := frAct L F posF m p
      decide (q < m * m) && F[q / m]! == ap L F[p / m]! && F[q % m]! == ap L F[p % m]! &&
        decide (ap T.pos q < T.pts.size) && ap T.pts (ap T.pos q) == q) &&
    (k == 0 || (decide (ap T.par k < k) && lv.contains (ap T.lab k) &&
      F[p / m]! == ap Ls[ap T.lab k]! F[ap T.pts (ap T.par k) / m]! &&
      F[p % m]! == ap Ls[ap T.lab k]! F[ap T.pts (ap T.par k) % m]!))

@[expose] def frNotIn (F posF : Array Nat) (m : Nat) (T : Tree) (u v : Nat) : Bool :=
  let i := posF[u]!
  let j := posF[v]!
  !(decide (i < m) && decide (j < m) && F[i]! == u && F[j]! == v) ||
    !(decide (ap T.pos (i * m + j) < T.pts.size) && ap T.pts (ap T.pos (i * m + j)) == i * m + j)

@[expose] def frBfsOK (c : Ctx) : Bool :=
  let c0 := frPt c frWc0
  let c1 := frPt c frWc1
  let xT := frX c c0 c1
  let F := frF c
  let m := F.size
  let posF := frPos F
  let lv := levelLetters c.L chainBase 2
  let root := posF[c0]! * m + posF[c1]!
  let T := frBfs c.L lv F posF root
  let Th := wordTab c frH0
  frWordsOK c && decide (m * m < 2 ^ 32) && F.all (fun a => decide (a < nPts)) &&
    allIn 0 m (fun i => posF[F[i]!]! == i) &&
    decide (posF[c0]! < m) && decide (posF[c1]! < m) &&
    F[posF[c0]!]! == c0 && F[posF[c1]!]! == c1 &&
    decide (0 < T.pts.size) && ap T.pts 0 == root && T.pts.size == frOrbitSize &&
    allIn 0 T.pts.size (frAt c.L lv F posF m T) &&
    ap Th c0 == 0 && ap Th c1 == 305530 &&
    (frLam c c0 c1).all (fun a => frNotIn F posF m T (ap Th a) (ap Th (ap xT a)))

end CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native
