module

public import Certificates.Data.CFSGNative.Fi24.Certificate

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native

set_option compiler.extract_closed false

@[expose] def packedN (O : Enum) : Table :=
  Array.ofFn (n := nPts) fun i => O.par[i.1]! ||| (O.lab[i.1]! <<< 30)

@[expose] def gensN (O : Enum) (l : Nat) : Table := if l = 1 then O.alpha else O.beta

@[expose] def gensInvN (O : Enum) (bInv : Table) (l : Nat) : Table :=
  if l = 1 then O.alpha else bInv

@[expose] def clsAtN (O : Enum) (bInv pl tP : Table) (k : Nat) (q : Array Nat) : Array Nat :=
  applyTree pl (gensN O) k (apT tP (applyTreeInv pl (gensInvN O bInv) k q))

@[expose] def letterJN (L : Array Table) (z : Int) : Table :=
  if 0 < z then L[2 * (z.natAbs - 1)]! else L[2 * (z.natAbs - 1) + 1]!

@[expose] def tPTableN (O : Enum) (tA tB : Table) : Table := Id.run do
  let mut t : Table := Array.replicate nPts 0
  for p in [1:nPts] do
    let q := ap t (ap O.par p)
    let v := if ap O.lab p == 1 then ap tA q else ap tB q
    t := t.set! p (UInt32.ofNat v)
  return t

@[expose] def normWordsN : Array (List Int) := #[
  [1, 4, 8, -13, 9, 3, -10, -5, -5, -8, 5, 5, 12, -8, -8, -8, 13, 8, 7, -12, 13, -10],
  [3, 9, 7, -3, 2, -6, -6, 11, 4, -7, -5, -13, 11, 10, 5, 7, -8, -7, 8, -11, 8, 9, -11, 13, 9,
    13]]

structure Ctx where
  O : Enum
  L : Array Table
  tP : Table
  pl : Table
  bInv : Table

@[expose] def mkCtx (O : Enum) : Ctx :=
  let L := chainLetters O
  ⟨O, L, tPTableN O (wordT nPts (letterJN L) normWordsN[0]!)
    (wordT nPts (letterJN L) normWordsN[1]!), packedN O, invT nPts O.beta⟩

@[expose] def clsPt (c : Ctx) (k p : Nat) : Nat := (clsAtN c.O c.bInv c.pl c.tP k #[p])[0]!

@[expose] def commB (c : Ctx) (k l : Nat) : Bool := clsPt c k l == l

@[expose] def clsTab (c : Ctx) (k : Nat) : Table :=
  (clsAtN c.O c.bInv c.pl c.tP k (Array.range nPts)).map UInt32.ofNat

@[expose] def wordTab (c : Ctx) (w : List Nat) : Table :=
  w.foldr (fun l T => compT nPts c.L[l]! T) (idT nPts)

@[inline, expose] def offTriple (s s2 t : Table) (k : Nat) : Bool :=
  let x := ap t k
  x != k && x != ap s k && x != ap s2 k

@[expose] def vecOf (c : Ctx) (T : Array Nat) (d : Nat) : Array Bool :=
  let img := clsAtN c.O c.bInv c.pl c.tP d T
  (Array.range T.size).map fun j => img[j]! == T[j]!

@[expose] def sepOK (c : Ctx) (F : Array Nat) (V : Array (Array Bool)) : Bool :=
  allIn 0 F.size fun i => allIn (i + 1) F.size fun j => V[i]! != V[j]! || !commB c F[i]! F[j]!

@[expose] def p1OK (V : Array (Array Bool)) : Bool := V.all fun v => v.contains false

@[expose] def bGensOK (c : Ctx) (s s2 : Table) (Ts : Array Table) : Bool :=
  allIn 0 nPts fun k => ap s k == k || Ts.any (fun t => offTriple s s2 t k) || !commB c k (ap s k)

@[expose] def fixCheck (c : Ctx) (w : List Nat) (m y : Nat) (T : Array Nat)
    (gp : Array (Nat × Nat)) : Bool :=
  let s := wordTab c w
  let s2 := compT nPts s s
  let F := (Array.range nPts).filter fun i => ap s i == i
  let V := F.map (vecOf c T)
  let Ts := gp.map fun e => compT nPts (clsTab c e.1) (clsTab c e.2)
  w.all (fun l => decide (l < c.L.size)) && order3OK nPts s && decide (m < nPts) && ap s m != m &&
    ap s 0 == 0 && ap s 305530 == 305530 && ap s 5604 == 5604 && decide (y < nPts) &&
    ap s y == y && T.all (fun t => decide (t < nPts) && ap s t == t) &&
    gp.all (fun e => decide (e.1 < nPts) && decide (e.2 < nPts) && ap s e.1 == e.1 &&
      ap s e.2 == e.2) &&
    sepOK c F V && p1OK V && bGensOK c s s2 Ts

@[expose] def lvl3TreeOK (c : Ctx) (y sz : Nat) : Bool :=
  let lv := levelLetters c.L chainBase 3
  let T := treeBFS nPts y c.L lv
  treeOK nPts y T c.L lv && T.pts.size == sz

@[expose] def uTab (c : Ctx) (s s2 : Table) (k : Nat) : Table :=
  compT nPts (clsTab c k) (compT nPts (clsTab c (ap s k)) (clsTab c (ap s2 k)))

@[expose] def uPt (c : Ctx) (s s2 : Table) (k p : Nat) : Nat :=
  clsPt c k (clsPt c (ap s k) (clsPt c (ap s2 k) p))

@[expose] def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, p => p
  | n + 1, p => iterN f n (f p)

@[expose] def retTime (f : Nat → Nat) (p bound : Nat) : Nat := Id.run do
  let mut q := f p
  let mut t := 1
  for _ in [0:bound] do
    if q == p then return t
    q := f q
    t := t + 1
  return 0

@[expose] def cycOK (f : Nat → Nat) (p L : Nat) : Bool :=
  L % 3 == 0 && L != 0 && iterN f L p == p && iterN f (L / 3) p != p

@[expose] def cyc3 (f : Nat → Nat) (p : Nat) : Bool := cycOK f p (retTime f p 64)

@[expose] def critAt (c : Ctx) (s s2 u0 : Table) (Cs : Array Table) (x : Nat) : Bool :=
  cyc3 (fun p => ap u0 (uPt c s s2 x p)) 0 ||
    Cs.any fun C =>
      cyc3 (fun p => ap u0 (uPt c s s2 x (ap C (ap u0 (uPt c s s2 x (ap C p)))))) 0

@[expose] def freeCheck (c : Ctx) (w : List Nat) (d0 : Nat) (gk ck : Array Nat)
    (dv : Array (Nat × Nat)) (bk bl : Nat) : Bool :=
  let s := wordTab c w
  let s2 := compT nPts s s
  let qB : Array Bool := (Array.range nPts).map fun i => commB c i (ap s i)
  let u0 := uTab c s s2 d0
  let Cs := ck.map (uTab c s s2)
  let lets : Array Table := #[s] ++ gk.map (uTab c s s2)
  let lv : Array Nat := Array.range lets.size
  let T0 := treeBFS nPts d0 lets lv
  let tB := compT nPts (uTab c s s2 bk) (uTab c s s2 bl)
  w.all (fun l => decide (l < c.L.size)) && order3OK nPts s &&
    allIn 0 nPts (fun i => ap s i != i) &&
    decide (d0 < nPts) && qB[d0]! && gk.all (fun k => decide (k < nPts) && qB[k]!) &&
    ck.all (fun k => decide (k < nPts) && qB[k]!) &&
    decide (bk < nPts) && qB[bk]! && decide (bl < nPts) && qB[bl]! &&
    treeOK nPts d0 T0 lets lv && allIn 0 nPts (fun x => !qB[x]! || inTreeB T0 x) &&
    allIn 0 nPts (fun x => !qB[x]! || x == d0 || x == ap s d0 || x == ap s2 d0 ||
      !(decide (x ≤ ap s x) && decide (x ≤ ap s2 x)) || critAt c s s2 u0 Cs x) &&
    dv.size == 6 && allIn 0 6 (fun i =>
      decide (dv[i]!.1 < nPts) && decide (dv[i]!.2 < nPts) && qB[dv[i]!.1]! && qB[dv[i]!.2]! &&
        clsPt c dv[i]!.1 dv[i]!.2 == chainBase[i]!) &&
    allIn 0 nPts (fun x => !qB[x]! || offTriple s s2 tB x)

@[expose] def tests0 : Array Nat := #[3699, 173820, 91201, 90254, 205084, 65416, 305940, 198646,
  277135, 250078, 170601, 104116, 225104, 139539, 31772, 219213, 115776, 86306, 108356, 279190,
  157865, 131669, 33055, 119203, 61148, 271741, 41254, 24790, 97146, 119292, 194617, 267453,
  192836, 122811, 184388, 141639, 158748, 274000, 100301, 277004, 106167, 241150, 189877, 85435,
  191662, 132341, 104713, 186229, 89527, 48946, 192799, 56478]

@[expose] def tests1 : Array Nat :=
  #[80106, 133281, 17126, 147071, 105282, 181685, 77099, 33437, 212478, 298823, 180175]

@[expose] def tests2 : Array Nat := #[303935, 67346, 298831, 185939, 276620, 99594, 51456, 41700]

@[expose] def tests3 : Array Nat := #[41478, 175773, 125411, 289342, 247226, 303694]

@[expose] def pairs0 : Array (Nat × Nat) := #[(13603, 161403), (243090, 211935), (27369, 255758)]

@[expose] def pairs1 : Array (Nat × Nat) := #[(303961, 275362), (46170, 157486), (185991, 117044)]

@[expose] def pairs2 : Array (Nat × Nat) := #[(92751, 238849), (126864, 155750), (33032, 40391)]

@[expose] def pairs3 : Array (Nat × Nat) := #[(31725, 39399), (298845, 40854), (167351, 177360)]

@[expose] def freeGens : Array Nat := #[130121, 223319, 11218]

@[expose] def freeConj : Array Nat := #[130121, 223319, 11218, 214695, 76631, 152916]

@[expose] def freeBase : Array (Nat × Nat) :=
  #[(149, 225340), (412, 6451), (28, 91325), (28, 33906), (266275, 266275), (122, 252791)]

@[expose] def fi24ThreeCheck (O : Enum) : Bool :=
  let c := mkCtx O
  fixCheck c [18] 1 221549 tests0 pairs0 && fixCheck c [16, 19] 1 221549 tests1 pairs1 &&
    fixCheck c [14, 16, 16, 14, 16, 16] 1 14069 tests2 pairs2 && lvl3TreeOK c 14069 1152 &&
    fixCheck c [16] 1 221549 tests3 pairs3 &&
    freeCheck c [2] 12 freeGens freeConj freeBase 11218 42290

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
