module

public import CFSG.Sporadic.Co1.Module.FormsInputs

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Pairs

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[expose] def parity24 (x : ℕ) : Bool :=
  (List.range 24).foldl (fun acc j => acc ^^ x.testBit j) false

@[expose] def q0N (c : ℕ) : Bool := parity24 (vecMulN 24 qRows c &&& c)

@[expose] def inPts (pts : Array ℕ) (pos : Array UInt32) (n w : ℕ) : Bool :=
  decide ((pos[w]!).toNat < n) && pts[(pos[w]!).toNat]! == w

@[expose] def tyLab (pts : Array ℕ) (pos : Array UInt32) (n w : ℕ) : ℕ :=
  if w = 0 then 0 else if q0N w then 2 else if inPts pts pos n w then 3 else 1

@[expose] def labCheck (D : VecData) : Bool :=
  let O := D.orbit ()
  let R0 := regs0 D O
  let st := runSLP D.n D.prog R0
  let L := lettersOf D.n D.sel st.1
  let lv := levelLetters L D.base 1
  let S := D.subReps.map fun r => treeBFS D.n r L lv
  let labs := labelsOf D.n S
  let pos := posTable D.d O.pts
  (List.range D.n).all fun p => labs[p]! == tyLab O.pts pos D.n (O.pts[0]! ^^^ O.pts[p]!)

@[expose] def witnessCheck : Bool :=
  let O := orbitOf 2 98280
  let pos := posTable 24 O.pts
  tyLab O.pts pos 98280 24 == 1 && tyLab O.pts pos 98280 (24 ^^^ 2) == 1

@[expose] def upd {α : Type*} (f : ℕ → α) (k : ℕ) (v : α) : ℕ → α :=
  fun r => if r = k then v else f r

@[expose] def runWith {α : Type*} (mul : α → α → α) (pow : α → ℕ → α) :
    List Instr → (ℕ → α) → ℕ → α
  | [], regs => regs
  | .mu i j k :: prog, regs => runWith mul pow prog (upd regs k (mul (regs i) (regs j)))
  | .pwr e i k :: prog, regs => runWith mul pow prog (upd regs k (pow (regs i) e))
  | .iv _ _ :: prog, regs => runWith mul pow prog regs

@[expose] def mclProg : List Instr :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 4 8, .mu 3 8 9, .pwr 22 4 5,
   .pwr 20 3 6, .mu 5 6 10, .pwr 18 4 11, .mu 10 11 1, .pwr 14 8 3, .mu 3 3 4, .mu 7 9 5,
   .pwr 6 5 7, .mu 4 7 8, .mu 8 3 2, .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7,
   .mu 7 4 8, .mu 3 8 9, .mu 9 4 10, .mu 10 10 11, .mu 11 11 9, .mu 10 11 8, .mu 9 8 1,
   .mu 3 3 10, .mu 5 5 11, .mu 11 11 8, .mu 10 8 9, .mu 6 6 10, .mu 10 10 11, .mu 10 11 6,
   .pwr 11 9 8, .mu 8 6 10, .mu 10 9 2]

@[expose] def mclRegs : ℕ → Array ℕ := fun r =>
  if r = 1 then dat.rowsA else if r = 2 then dat.rowsB else idRows 24

@[expose] def mclRun : ℕ → Array ℕ := runWith (mulRows 24) (powRows 24) mclProg mclRegs

@[expose] def bfsTree (f : ℕ → ℕ → ℕ) (w0 cap : ℕ) : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut pts : Array ℕ := #[w0]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  for h in [0:cap] do
    if h < pts.size then
      for l in [0:2] do
        let w := f l pts[h]!
        if !pts.contains w then
          pts := pts.push w
          par := par.push h
          lab := lab.push l
    else break
  return (pts, par, lab)

@[expose] def treeCheckV (f : ℕ → ℕ → ℕ) (L par lab : Array ℕ) : Bool :=
  decide (0 < L.size) && (List.range L.size).all fun k =>
    k == 0 || (decide (par[k]! < k) && decide (lab[k]! < 2) && L[k]! == f lab[k]! L[par[k]!]!)

@[expose] def distinctB (L : Array ℕ) : Bool :=
  (List.range L.size).all fun i => (List.range i).all fun j => L[i]! != L[j]!

@[expose] def allLtB (L : Array ℕ) (b : ℕ) : Bool :=
  (List.range L.size).all fun k => decide (L[k]! < b)

@[expose] def mclCheckT (O : VOrbit) (f : ℕ → ℕ → ℕ) (x0 u w0 : ℕ) (L par lab : Array ℕ) :
    Bool :=
  let pos := posTable 24 O.pts
  let y0 := x0 ^^^ u
  let inO := inPts O.pts pos 98280
  inO x0 && inO y0 && q0N u && f 0 x0 == x0 && f 0 y0 == y0 && f 1 x0 == x0 && f 1 y0 == y0 &&
    inO w0 && inO (x0 ^^^ w0) && inO (w0 ^^^ y0) && L[0]! == w0 && L.size == 275 &&
    allLtB L (2 ^ 24) && treeCheckV f L par lab && distinctB L &&
    (List.range 98280).all fun p =>
      !(inO (x0 ^^^ O.pts[p]!) && inO (O.pts[p]! ^^^ y0)) || L.contains O.pts[p]!

@[expose] def mclAct (R1 R2 : Array ℕ) : ℕ → ℕ → ℕ := fun l x =>
  vecMulN 24 (if l = 0 then transposeRows 24 R1 else transposeRows 24 R2) x

@[expose] def mclCheckOf (O : VOrbit) (R1 R2 : Array ℕ) (x0 u w0 : ℕ) : Bool :=
  mclCheckT O (mclAct R1 R2) x0 u w0 (bfsTree (mclAct R1 R2) w0 400).1
    (bfsTree (mclAct R1 R2) w0 400).2.1 (bfsTree (mclAct R1 R2) w0 400).2.2

@[expose] def mclCheck : Bool :=
  mclCheckOf (orbitOf 2 98280) (mclRun 1) (mclRun 2) 16663704 4852818 4473570

@[expose] def pairsCheck : Bool :=
  (orbitOf 2 98280).pts[0]! == 2 && labCheck dat && witnessCheck && mclCheck

end CFSG.Sporadic.Co1.Module.Pairs
