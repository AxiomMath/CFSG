module

public import Certificates.Data.CFSGNative.F3.Basic

public section

namespace CFSG.KC.LQT.Fast

open CFSG.F3.Native

partial def digitsInto (w x n : Nat) (acc : Array Nat) : Array Nat :=
  if n ≤ 8 then Id.run do
    let m := (1 <<< w) - 1
    let mut acc := acc
    let mut x := x
    for _ in [0:n] do
      acc := acc.push (x &&& m)
      x := x >>> w
    return acc
  else
    let h := n / 2
    digitsInto w (x >>> (w * h)) (n - h) (digitsInto w (x &&& ((1 <<< (w * h)) - 1)) h acc)

partial def packRange (w : Nat) (ds : Array Nat) (lo n : Nat) : Nat :=
  if n ≤ 8 then Id.run do
    let mut x := 0
    for k in [0:n] do
      x := (x <<< w) ||| ds[lo + n - 1 - k]!
    return x
  else
    let h := n / 2
    packRange w ds lo h ||| (packRange w ds (lo + h) (n - h) <<< (w * h))

def toRows (w d x : Nat) : Array V :=
  let ds := digitsInto w x (d * d) (Array.mkEmpty (d * d))
  Array.ofFn (n := d) fun i => V.ofFn d fun j => ds[i.val * d + j]!

def ofRows (w d : Nat) (X : Array V) : Nat := Id.run do
  let mut ds : Array Nat := Array.mkEmpty (d * d)
  for i in [0:d] do
    let r := X[i]!
    for j in [0:d] do
      ds := ds.push (r.get j)
  return packRange w ds 0 (d * d)

def mulPacked (w d A B : Nat) : Nat := ofRows w d (mul d (toRows w d A) (toRows w d B))

def decodePacked (w d : Nat) (s : String) : Nat :=
  let e := (decodeEntries s).toArray
  packRange w (Array.ofFn (n := d * d) fun k => (e[k.val]?.getD 0) % 3) 0 (d * d)

end CFSG.KC.LQT.Fast
