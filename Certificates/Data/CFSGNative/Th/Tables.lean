module

public import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.Th.Native

abbrev Table := Array UInt32

@[inline, expose] def ap (t : Table) (p : Nat) : Nat := (t[p]!).toNat

@[inline, expose] def none32 (_ : Unit := ()) : UInt32 := 0xFFFFFFFF

@[expose] def tblOfBytes (n : Nat) (b : ByteArray) : Table :=
  Array.ofFn (n := n) fun i => UInt32.ofNat (readU32 b i.val)

@[expose] def idT (n : Nat) : Table := Array.ofFn (n := n) fun i => UInt32.ofNat i.val

@[expose] def compT (n : Nat) (P Q : Table) : Table :=
  Array.ofFn (n := n) fun i => P[(Q[i.val]!).toNat]!

@[expose] def powT (n : Nat) : Nat → Table → Table
  | 0, _ => idT n
  | e + 1, P => compT n P (powT n e P)

@[expose] def invT (n : Nat) (P : Table) : Table := Id.run do
  let mut r : Table := Array.replicate n 0
  for i in [0:n] do
    r := r.set! (P[i]!).toNat (UInt32.ofNat i)
  return r

@[expose] def invOK (n : Nat) (P R : Table) : Bool := allIn 0 n fun i => ap R (ap P i) == i

@[expose] def invoOK (n : Nat) (P : Table) : Bool := allIn 0 n fun i => ap P (ap P i) == i

@[expose] def order3OK (n : Nat) (P : Table) : Bool := allIn 0 n fun i => ap P (ap P (ap P i)) == i

inductive Instr where
  | mu (i j k : Nat)
  | pwr (e i k : Nat)
  | iv (i k : Nat)

@[expose] def stepT (n : Nat) (st : Array Table × Bool) : Instr → Array Table × Bool
  | .mu i j k => (st.1.set! k (compT n st.1[i]! st.1[j]!), st.2)
  | .pwr e i k => (st.1.set! k (powT n e st.1[i]!), st.2)
  | .iv i k =>
    let r := invT n st.1[i]!
    (st.1.set! k r, st.2 && invOK n st.1[i]! r)

@[expose] def runSLP (n : Nat) (prog : List Instr) (regs : Array Table) : Array Table × Bool :=
  prog.foldl (stepT n) (regs, true)

@[expose] def wordT (n : Nat) (gens : Int → Table) (w : List Int) : Table :=
  w.foldr (fun l T => let L := gens l; T.map fun t => L[t.toNat]!) (idT n)

@[inline, expose] def apT (t : Table) (q : Array Nat) : Array Nat := Id.run do
  let mut q := q
  for k in [0:q.size] do
    q := q.set! k (ap t q[k]!)
  return q

@[expose] def applyTree (pl : Table) (gens : Nat → Table) (k : Nat) (q : Array Nat) : Array Nat :=
  if _h : 0 < k ∧ treePar (pl[k]!).toNat < k then
    apT (gens (treeLab (pl[k]!).toNat)) (applyTree pl gens (treePar (pl[k]!).toNat) q)
  else q
termination_by k

@[expose] def applyTreeInv (pl : Table) (gensInv : Nat → Table) (k : Nat) (q : Array Nat) :
    Array Nat :=
  if _h : 0 < k ∧ treePar (pl[k]!).toNat < k then
    applyTreeInv pl gensInv (treePar (pl[k]!).toNat) (apT (gensInv (treeLab (pl[k]!).toNat)) q)
  else q
termination_by k

@[expose] def localBFS (n root : Nat) (g1 g2 : Table) : Table × Table × Table := Id.run do
  let mut pos : Table := Array.replicate n none32
  let mut pts : Table := #[UInt32.ofNat root]
  let mut pl : Table := #[0]
  pos := pos.set! root 0
  for h in [0:n] do
    if h < pts.size then
      let p := (pts[h]!).toNat
      let a := ap g1 p
      if pos[a]! == none32 then
        pos := pos.set! a (UInt32.ofNat pts.size)
        pts := pts.push (UInt32.ofNat a)
        pl := pl.push (UInt32.ofNat (h ||| (1 <<< 30)))
      let b := ap g2 p
      if pos[b]! == none32 then
        pos := pos.set! b (UInt32.ofNat pts.size)
        pts := pts.push (UInt32.ofNat b)
        pl := pl.push (UInt32.ofNat (h ||| (2 <<< 30)))
    else break
  return (pts, pl, pos)

@[expose] def smallBFS (root cap : Nat) (g1 g2 : Table) : Table × Table := Id.run do
  let mut pts : Table := #[UInt32.ofNat root]
  let mut pl : Table := #[0]
  for h in [0:cap] do
    if h < pts.size then
      let p := (pts[h]!).toNat
      let a := ap g1 p
      if !pts.contains (UInt32.ofNat a) then
        pts := pts.push (UInt32.ofNat a)
        pl := pl.push (UInt32.ofNat (h ||| (1 <<< 30)))
      let b := ap g2 p
      if !pts.contains (UInt32.ofNat b) then
        pts := pts.push (UInt32.ofNat b)
        pl := pl.push (UInt32.ofNat (h ||| (2 <<< 30)))
    else break
  return (pts, pl)

@[expose] def findPt (pts : Table) (p : Nat) : Nat := Id.run do
  for k in [0:pts.size] do
    if (pts[k]!).toNat == p then return k
  return pts.size

@[inline, expose] def treeCheckAt (n m : Nat) (pts pl : Table) (lk : Nat → Nat) (g1 g2 : Table)
    (k : Nat) : Bool :=
  let p := ap pts k
  let a := ap g1 p
  let b := ap g2 p
  p < n && lk p == k && lk a < m && ap pts (lk a) == a && lk b < m && ap pts (lk b) == b &&
    (k == 0 ||
      (let r := (pl[k]!).toNat
       let par := treePar r
       let l := treeLab r
       par < k && ((l == 1 && ap g1 (ap pts par) == p) || (l == 2 && ap g2 (ap pts par) == p))))

@[expose] def treeOK (n m root : Nat) (pts pl : Table) (lk : Nat → Nat) (g1 g2 : Table) : Bool :=
  0 < m && ap pts 0 == root && allIn 0 m (treeCheckAt n m pts pl lk g1 g2)

end CFSG.Sporadic.Th.Native
