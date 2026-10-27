module

public import Certificates.Data.CFSGNative.Ly.Orbit
public import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native

structure Relabel where
  pts : Table
  pos : Table
  alpha : Table
  beta : Table
  par : Table
  lab : Table
deriving Inhabited

@[expose] def relabel (n : Nat) (alpha beta : Table) (r : Nat) : Relabel := Id.run do
  let mut pos : Table := (Array.replicate n none32).set! r 0
  let mut pts : Table := (Array.emptyWithCapacity n).push (UInt32.ofNat r)
  let mut par : Table := (Array.emptyWithCapacity n).push 0
  let mut lab : Table := (Array.emptyWithCapacity n).push 0
  for h in [0:n] do
    if h < pts.size then
      let x := ap pts h
      let ya := ap alpha x
      if ya < n && pos[ya]! == none32 then
        pos := pos.set! ya (UInt32.ofNat pts.size)
        pts := pts.push (UInt32.ofNat ya)
        par := par.push (UInt32.ofNat h)
        lab := lab.push 1
      let yb := ap beta x
      if yb < n && pos[yb]! == none32 then
        pos := pos.set! yb (UInt32.ofNat pts.size)
        pts := pts.push (UInt32.ofNat yb)
        par := par.push (UInt32.ofNat h)
        lab := lab.push 2
    else break
  let na : Table := Array.ofFn (n := pts.size) fun k => pos[ap alpha (ap pts k.val)]!
  let nb : Table := Array.ofFn (n := pts.size) fun k => pos[ap beta (ap pts k.val)]!
  return ⟨pts, pos, na, nb, par, lab⟩

@[expose] def relabelOK (n : Nat) (alpha beta : Table) (r : Nat) (R : Relabel) : Bool :=
  R.pts.size == n && R.alpha.size == n && R.beta.size == n && ap R.pts 0 == r &&
    allIn 0 n (fun k => decide (ap R.pts k < n) && ap R.pos (ap R.pts k) == k &&
      decide (ap R.alpha k < n) && ap R.pts (ap R.alpha k) == ap alpha (ap R.pts k) &&
      decide (ap R.beta k < n) && ap R.pts (ap R.beta k) == ap beta (ap R.pts k)) &&
    allIn 1 n (fun k => decide (ap R.par k < k) &&
      ((ap R.lab k == 1 && ap R.alpha (ap R.par k) == k) ||
        (ap R.lab k == 2 && ap R.beta (ap R.par k) == k)))

@[inline, expose] def relDiscPos (R : Relabel) (k : Nat) : Nat :=
  2 * ap R.par k + (ap R.lab k - 1)

@[expose] def relOrderOK (n : Nat) (R : Relabel) : Bool :=
  allIn 1 (n - 1) (fun k => relDiscPos R k < relDiscPos R (k + 1)) &&
    allIn 0 n (fun i => (ap R.alpha i == 0 || relDiscPos R (ap R.alpha i) ≤ 2 * i) &&
      (ap R.beta i == 0 || relDiscPos R (ap R.beta i) ≤ 2 * i + 1))

@[expose] def fixedMask (n : Nat) (xs : Array Nat) : Array Bool :=
  xs.foldl (fun m x => m.set! x true) (Array.replicate n false)

@[expose] def fixedOK (n : Nat) (alpha : Table) (fi : Array Nat) : Bool :=
  let m := fixedMask n fi
  fi.size == 2772 && allIn 0 (fi.size - 1) (fun k => fi[k]! < fi[k + 1]!) &&
    allIn 0 fi.size (fun k => fi[k]! < n) &&
    allIn 0 n (fun i => (ap alpha i == i) == m[i]!)

end CFSG.Sporadic.LySchreier.Native
