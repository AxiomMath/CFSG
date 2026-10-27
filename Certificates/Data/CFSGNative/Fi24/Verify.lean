module

public import Certificates.Data.CFSGNative.Fi24.Enum

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th.Native

@[expose] def formAt (gens : Unit → Gens) (E : Enum) (R0 : RRef) (k : Nat) : RRef :=
  if _h : 0 < k ∧ ap E.par k < k then
    stepForm ((gens ()).get (ap E.lab k)) (formAt gens E R0 (ap E.par k)).rows
  else R0
termination_by k

@[inline, expose] def Enum.st (E : Enum) (m : Nat) : Nat := E.starts[m]!

@[expose] def nextLevel (gens : Unit → Gens) (E : Enum) (chunks m : Nat) (cur : Array RRef) :
    Array RRef :=
  parRange (E.st (m + 1)) (E.st (m + 2)) chunks gens fun G k =>
    stepForm (G.get (ap E.lab k)) (cur[ap E.par k - E.st m]!).rows

@[expose] def skipEdge (E : Enum) (k g : Nat) : Bool :=
  if g = 1 then
    let j := ap E.alpha k
    j < k || (ap E.par j == k && ap E.lab j == 1)
  else
    let j := ap E.beta k
    (j < k && ap E.beta j < k) || (ap E.par j == k && ap E.lab j == 2)

@[inline, expose] def lookupForm (E : Enum) (m : Nat) (prev cur : Array RRef) (x : Nat) : RRef :=
  if E.st m ≤ x then cur[x - E.st m]! else prev[x - E.st (m - 1)]!

@[inline, expose] def Enum.inLevel (E : Enum) (m x : Nat) : Bool :=
  E.st m ≤ x && x < E.st (m + 1)

@[expose] def edgeCompare (G : Gens) (E : Enum) (m : Nat) (prev cur : Array RRef) (k g j : Nat) :
    Bool :=
  stepForm (G.get g) (lookupForm E m prev cur k).rows == lookupForm E m prev cur j

@[expose] def edgeCheck (G : Gens) (E : Enum) (m : Nat) (prev cur : Array RRef) (k g : Nat) :
    Bool :=
  if skipEdge E k g then true else
  let j := if g = 1 then ap E.alpha k else ap E.beta k
  if E.inLevel m k then
    if E.inLevel m j || (0 < m && E.inLevel (m - 1) j) then edgeCompare G E m prev cur k g j
    else E.inLevel (m + 1) j
  else
    if E.inLevel m j then edgeCompare G E m prev cur k g j else true

@[expose] def parAllWith {σ : Type} (lo hi chunks : Nat) (setup : Unit → σ)
    (p : σ → Nat → Bool) : Bool :=
  let c := chunks + 1
  ((List.range c).map fun j => Task.spawn fun _ =>
    let env := setup ()
    allStep j c (hi - lo) fun i => p env (lo + i)).all Task.get

@[expose] def checkLevel (gens : Unit → Gens) (E : Enum) (chunks m : Nat)
    (prev cur : Array RRef) : Bool :=
  parAllWith (if m = 0 then E.st 0 else E.st (m - 1)) (E.st (m + 1)) chunks gens fun G k =>
    (if E.st m ≤ k then rrefOK 253 cur[k - E.st m]! else true) &&
      edgeCheck G E m prev cur k 1 && edgeCheck G E m prev cur k 2

@[expose] def verifyFrom (gens : Unit → Gens) (E : Enum) (chunks : Nat) :
    Nat → Nat → Array RRef → Array RRef → Array UInt64 → Bool × Array UInt64
  | 0, _, _, _, hs => (false, hs)
  | fuel + 1, m, prev, cur, hs =>
    if checkLevel gens E chunks m prev cur then
      let hs := hs ++ cur.map fun F => hashRows F.rows
      if m + 2 < E.starts.size then
        verifyFrom gens E chunks fuel (m + 1) cur (nextLevel gens E chunks m cur) hs
      else (true, hs)
    else (false, hs)

@[expose] def enumOK (E : Enum) (n : Nat) : Bool :=
  let L := E.starts.size
  E.alpha.size == n && E.beta.size == n && E.par.size == n && E.lab.size == n &&
    3 ≤ L && E.st 0 == 0 && E.st 1 == 1 && E.st (L - 1) == n && ap E.lab 0 == 0 &&
    allIn 0 (L - 1) (fun m => E.st m < E.st (m + 1)) &&
    allIn 0 n (fun k => ap E.alpha k < n && ap E.beta k < n) &&
    invoOK n E.alpha && order3OK n E.beta &&
    allIn 1 (L - 1) (fun m => allIn (E.st m) (E.st (m + 1)) fun k =>
      let p := ap E.par k
      let l := ap E.lab k
      E.st (m - 1) ≤ p && p < E.st m &&
        ((l == 1 && ap E.alpha p == k) || (l == 2 && ap E.beta p == k)))

@[expose] def strictInc : List UInt64 → Bool
  | a :: b :: t => a < b && strictInc (b :: t)
  | _ => true

@[expose] def distinctHashes (hs : Array UInt64) : Bool :=
  strictInc (hs.toList.mergeSort fun a b => a ≤ b)

@[expose] def orbitVerify (gens : Unit → Gens) (E : Enum) (R0 : RRef) (n chunks : Nat) : Bool :=
  enumOK E n &&
    let res := verifyFrom gens E chunks E.starts.size 0 #[] #[R0] #[]
    res.1 && res.2.size == n && distinctHashes res.2

end CFSG.Sporadic.Fi24.Native
