module

public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.CFSGNative.Fi24.Wide

public section

namespace CFSG.KC.LQT.Mul3

open CFSG.F3.Native
open CFSG.Sporadic.Fi24.Native (W)

@[inline] def limb (x l : Nat) : UInt64 := (x >>> (64 * l)).toUInt64

def wOfV (a : V) : W :=
  ⟨limb a.p 0, limb a.p 1, limb a.p 2, limb a.p 3, limb a.p 4, limb a.p 5, limb a.p 6, limb a.p 7,
    limb a.p 8, limb a.p 9, limb a.p 10, limb a.p 11, limb a.p 12, limb a.m 0, limb a.m 1,
    limb a.m 2, limb a.m 3, limb a.m 4, limb a.m 5, limb a.m 6, limb a.m 7, limb a.m 8, limb a.m 9,
    limb a.m 10, limb a.m 11, limb a.m 12⟩

def vOfW (a : W) : V := Id.run do
  let mut p := 0
  let mut m := 0
  for l in [0:13] do
    p := p ||| ((a.limbP l).toNat <<< (64 * l))
    m := m ||| ((a.limbM l).toNat <<< (64 * l))
  return ⟨p, m⟩

def mulW (d : Nat) (X Y : Array W) : Array W := Id.run do
  let mut acc : Array W := Array.replicate X.size W.zero
  for g8 in [0:(d + 7) / 8] do
    let g := 8 * g8
    let mut T : Array W := Array.mkEmpty 256
    T := T.push W.zero
    for b in [0:8] do
      let y := Y[g + b]?.getD W.zero
      for s in [0:1 <<< b] do
        T := T.push (T[s]!.add y)
    let l := g / 64
    let sh := (g % 64).toUInt64
    for i in [0:X.size] do
      let x := X[i]!
      let bp := ((x.limbP l >>> sh) &&& 255).toNat
      let bm := ((x.limbM l >>> sh) &&& 255).toNat
      if bp != 0 || bm != 0 then
        let mut a := acc[i]!
        if bp != 0 then a := a.add T[bp]!
        if bm != 0 then a := a.sub T[bm]!
        acc := acc.set! i a
  return acc

def mulFR (d : Nat) (X Y : Array V) : Array V := Id.run do
  if d ≤ 832 then return (mulW d (X.map wOfV) (Y.map wOfV)).map vOfW
  let mut acc : Array V := Array.replicate X.size V.zero
  for g8 in [0:(d + 7) / 8] do
    let g := 8 * g8
    let mut T : Array V := Array.mkEmpty 256
    T := T.push V.zero
    for b in [0:8] do
      let y := Y[g + b]?.getD V.zero
      for s in [0:1 <<< b] do
        T := T.push (T[s]!.add y)
    for i in [0:X.size] do
      let x := X[i]!
      let bp := (x.p >>> g) &&& 255
      let bm := (x.m >>> g) &&& 255
      if bp != 0 || bm != 0 then
        let mut a := acc[i]!
        if bp != 0 then a := a.add T[bp]!
        if bm != 0 then a := a.sub T[bm]!
        acc := acc.set! i a
  return acc

def digApp (d : Nat) (Xs : Array (Array V)) (n : Nat) (v : V) : V := Id.run do
  let mut n := n
  let mut v := v
  for X in Xs do
    for _ in [0:n % 3] do
      v := comb d X v
    n := n / 3
  return v

def spreadTbl (w : Nat) : Array Nat := Id.run do
  let mut T : Array Nat := Array.mkEmpty 65536
  T := T.push 0
  for x in [1:65536] do
    T := T.push ((T[x / 2]! <<< w) ||| (x % 2))
  return T

partial def spread (w : Nat) (tbl : Array Nat) (x n : Nat) : Nat :=
  if x == 0 then 0
  else if n ≤ 16 then tbl[x]!
  else
    let h := if 32 ≤ n then 16 * (n / 32) else 16
    spread w tbl (x &&& ((1 <<< h) - 1)) h ||| (spread w tbl (x >>> h) (n - h) <<< (w * h))

partial def joinRows (S : Nat) (rs : Array Nat) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi == lo + 1 then rs[lo]!
  else
    let mid := (lo + hi) / 2
    joinRows S rs lo mid ||| (joinRows S rs mid hi <<< (S * (mid - lo)))

def toLane (w d : Nat) (tbl : Array Nat) (R : Array V) : Nat :=
  joinRows (w * d) (R.map fun r => spread w tbl r.p d ||| (spread w tbl r.m d <<< 1)) 0 R.size

end CFSG.KC.LQT.Mul3

end
