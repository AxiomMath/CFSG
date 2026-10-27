module

public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native

structure W where
  p0 : UInt64
  p1 : UInt64
  p2 : UInt64
  p3 : UInt64
  m0 : UInt64
  m1 : UInt64
  m2 : UInt64
  m3 : UInt64
deriving Inhabited, DecidableEq, Hashable

@[inline, expose] def addP (ap am bp bm : UInt64) : UInt64 :=
  (ap ^^^ (ap &&& (bp ||| bm))) ||| (bp ^^^ (bp &&& (ap ||| am))) ||| (am &&& bm)

@[inline, expose] def addM (ap am bp bm : UInt64) : UInt64 :=
  (am ^^^ (am &&& (bp ||| bm))) ||| (bm ^^^ (bm &&& (ap ||| am))) ||| (ap &&& bp)

@[inline, expose] def W.add (a b : W) : W :=
  ⟨addP a.p0 a.m0 b.p0 b.m0, addP a.p1 a.m1 b.p1 b.m1, addP a.p2 a.m2 b.p2 b.m2,
    addP a.p3 a.m3 b.p3 b.m3, addM a.p0 a.m0 b.p0 b.m0, addM a.p1 a.m1 b.p1 b.m1,
    addM a.p2 a.m2 b.p2 b.m2, addM a.p3 a.m3 b.p3 b.m3⟩

@[inline, expose] def W.neg (a : W) : W := ⟨a.m0, a.m1, a.m2, a.m3, a.p0, a.p1, a.p2, a.p3⟩

@[inline, expose] def W.sub (a b : W) : W := a.add b.neg

@[inline, expose] def W.zero : W := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline, expose] def W.limbP (a : W) (l : Nat) : UInt64 :=
  if l = 0 then a.p0 else if l = 1 then a.p1 else if l = 2 then a.p2 else if l = 3 then a.p3
  else 0

@[inline, expose] def W.limbM (a : W) (l : Nat) : UInt64 :=
  if l = 0 then a.m0 else if l = 1 then a.m1 else if l = 2 then a.m2 else if l = 3 then a.m3
  else 0

@[inline, expose] def W.bitP (a : W) (j : Nat) : Bool :=
  (a.limbP (j >>> 6) >>> (j &&& 63).toUInt64) &&& 1 != 0

@[inline, expose] def W.bitM (a : W) (j : Nat) : Bool :=
  (a.limbM (j >>> 6) >>> (j &&& 63).toUInt64) &&& 1 != 0

@[expose] def combW (d : Nat) (Y : Array W) (r : W) : W :=
  Nat.fold d (fun j _ acc => if r.bitP j then acc.add Y[j]!
    else if r.bitM j then acc.sub Y[j]! else acc) W.zero

@[expose] def mulW (d : Nat) (X Y : Array W) : Array W := X.map (combW d Y)

@[inline, expose] def conjW (d : Nat) (g gi X : Array W) : Array W := mulW d (mulW d g X) gi

@[inline, expose] def join (x0 x1 x2 x3 : UInt64) : Nat :=
  x0.toNat ||| (x1.toNat <<< 64) ||| (x2.toNat <<< 128) ||| (x3.toNat <<< 192)

@[inline, expose] def W.toV (a : W) : V := ⟨join a.p0 a.p1 a.p2 a.p3, join a.m0 a.m1 a.m2 a.m3⟩

@[expose] def ofV (v : V) : W :=
  ⟨UInt64.ofNat v.p, UInt64.ofNat (v.p >>> 64), UInt64.ofNat (v.p >>> 128),
    UInt64.ofNat (v.p >>> 192), UInt64.ofNat v.m, UInt64.ofNat (v.m >>> 64),
    UInt64.ofNat (v.m >>> 128), UInt64.ofNat (v.m >>> 192)⟩

@[expose] def idW (d : Nat) : Array W := (idM d).map ofV

@[expose] def powW (d : Nat) (M : Array W) : Nat → Array W
  | 0 => idW d
  | e + 1 => mulW d (powW d M e) M

@[expose] def prodW (d : Nat) (mats : Array (Array W)) (word : List Nat) : Array W :=
  word.foldl (fun M x => mulW d M mats[x]!) (idW d)

@[inline, expose] def eqW (d : Nat) (X Y : Array W) : Bool := X.size == d && decide (X = Y)

@[inline, expose] def W.wf (a : W) : Bool :=
  a.p0 &&& a.m0 == 0 && a.p1 &&& a.m1 == 0 && a.p2 &&& a.m2 == 0 && a.p3 &&& a.m3 == 0

@[inline, expose] def W.canon (d : Nat) (a : W) : Bool :=
  a.wf && a.p3 >>> (d - 192).toUInt64 == 0 && a.m3 >>> (d - 192).toUInt64 == 0

@[expose] def canonW (d : Nat) (X : Array W) : Bool := X.size == d && X.all (W.canon d)

@[expose] def toVM (X : Array W) : Array V := X.map W.toV

structure WOrbit where
  keys : Array (Array W)
  alpha : Table
  beta : Table
  par : Table
  lab : Table
deriving Inhabited

@[expose] def parMapRange {α : Type} (lo hi chunks : Nat) (f : Nat → α) : Array α :=
  let c := chunks + 1
  let per := (hi - lo + c - 1) / c
  let tasks := (List.range c).map fun t => Task.spawn fun _ =>
    let s := lo + t * per
    let e := min hi (s + per)
    (Array.range (e - s)).map fun i => f (s + i)
  tasks.foldl (fun acc tk => acc ++ tk.get) #[]

@[inline, expose] def getT (t : Table) (i : Nat) : Option Nat :=
  match t[i]? with
  | some x => if x == none32 then none else some x.toNat
  | none => none

@[expose] def conjBFSW (d : Nat) (R A Ai B Bi : Array W) (cap chunks : Nat) : WOrbit := Id.run do
  let mut keys : Array (Array W) := #[R]
  let mut index : Std.HashMap (Array W) Nat := (∅ : Std.HashMap _ _).insert R 0
  let mut alpha : Table := #[none32]
  let mut beta : Table := #[none32]
  let mut binv : Table := #[none32]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  let mut lo := 0
  for _ in [0:cap] do
    if lo < keys.size then
      let hi := keys.size
      let ks := keys
      let al := alpha
      let bi := binv
      let imgs := parMapRange lo hi chunks fun h =>
        (if (getT al h).isSome then none else some (conjW d A Ai ks[h]!),
          match getT bi h with
          | some p => if (getT bi p).isSome then none else some (conjW d B Bi ks[h]!)
          | none => some (conjW d B Bi ks[h]!))
      for i in [0:hi - lo] do
        let h := lo + i
        if (getT alpha h).isNone then
          let Ya := imgs[i]!.1.getD #[]
          match index[Ya]? with
          | some k =>
            alpha := (alpha.set! h (UInt32.ofNat k)).set! k (UInt32.ofNat h)
          | none =>
            let k := keys.size
            index := index.insert Ya k
            keys := keys.push Ya
            par := par.push (UInt32.ofNat h)
            lab := lab.push 1
            alpha := (alpha.push none32).set! h (UInt32.ofNat k) |>.set! k (UInt32.ofNat h)
            beta := beta.push none32
            binv := binv.push none32
        let derived := match getT binv h with
          | some p => getT binv p
          | none => none
        match derived with
        | some q => beta := beta.set! h (UInt32.ofNat q)
        | none =>
          let Yb := imgs[i]!.2.getD #[]
          match index[Yb]? with
          | some k =>
            beta := beta.set! h (UInt32.ofNat k)
            binv := binv.set! k (UInt32.ofNat h)
          | none =>
            let k := keys.size
            index := index.insert Yb k
            keys := keys.push Yb
            par := par.push (UInt32.ofNat h)
            lab := lab.push 2
            alpha := alpha.push none32
            beta := (beta.push none32).set! h (UInt32.ofNat k)
            binv := (binv.push none32).set! k (UInt32.ofNat h)
      lo := hi
    else break
  return ⟨keys, alpha, beta, par, lab⟩

@[expose] def indexOfW (keys : Array (Array W)) : Std.HashMap (Array W) Nat :=
  (List.range keys.size).foldl (fun m i => m.insert keys[i]! i) ∅

@[inline, expose] def conjCheckAtW (d : Nat) (A Ai B Bi : Array W) (O : WOrbit)
    (pos : Array W → Nat) (k : Nat) : Bool :=
  let N := O.keys.size
  let X := O.keys[k]!
  let ka := ap O.alpha k
  let kb := ap O.beta k
  canonW d X && pos X == k && ka < N && kb < N &&
    (ka < k || eqW d (conjW d A Ai X) O.keys[ka]!) &&
    ((kb < k && ap O.beta kb < k) || eqW d (conjW d B Bi X) O.keys[kb]!) &&
    (k == 0 || (ap O.par k < k &&
      ((ap O.lab k == 1 && ap O.alpha (ap O.par k) == k) ||
        (ap O.lab k == 2 && ap O.beta (ap O.par k) == k))))

@[expose] def conjOrbitOKW (d : Nat) (R A Ai B Bi : Array W) (O : WOrbit) (chunks : Nat) : Bool :=
  let index := indexOfW O.keys
  0 < O.keys.size && O.keys.size < 2 ^ 32 && eqW d O.keys[0]! R &&
    invoOK O.keys.size O.alpha && order3OK O.keys.size O.beta &&
    parAll O.keys.size chunks
      (conjCheckAtW d A Ai B Bi O (fun X => index.getD X O.keys.size))

end CFSG.Sporadic.Fi23.Native
