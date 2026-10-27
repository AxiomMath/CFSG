module

public import Certificates.Data.CFSGNative.Ly.Pack
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Ly.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def mul7 (X Y : Array Nat) : Array Nat :=
  Array.ofFn (n := 49) fun t =>
    let a := 7 * (t.val / 7)
    let b := t.val % 7
    (Nat.fold 7 (fun l _ acc => acc + X[a + l]! * Y[7 * l + b]!) 0) % 5

@[expose] def id7 (_ : Unit := ()) : Array Nat :=
  Array.ofFn (n := 49) fun t => if t.val / 7 = t.val % 7 then 1 else 0

@[inline, expose] def inv5 (x : Nat) : Nat := x ^ 3 % 5

@[expose] def inv7 (X : Array Nat) : Array Nat := Id.run do
  let mut A : ByteArray := ⟨Array.ofFn (n := 98) fun t =>
    let i := t.val / 14
    let j := t.val % 14
    UInt8.ofNat (if j < 7 then X[7 * i + j]! % 5 else if j - 7 = i then 1 else 0)⟩
  for c in [0:7] do
    let mut piv := 7
    for r in [c:7] do
      if piv == 7 && A.get! (14 * r + c) != 0 then piv := r
    if piv < 7 then
      if piv != c then
        for j in [0:14] do
          let x := A.get! (14 * piv + j)
          A := (A.set! (14 * piv + j) (A.get! (14 * c + j))).set! (14 * c + j) x
      let iv := UInt8.ofNat (inv5 (A.get! (14 * c + c)).toNat)
      for j in [0:14] do
        A := A.set! (14 * c + j) (A.get! (14 * c + j) * iv % 5)
      for r in [0:7] do
        if r != c then
          let f := A.get! (14 * r + c)
          if f != 0 then
            let g := 5 - f
            for j in [0:14] do
              A := A.set! (14 * r + j) ((A.get! (14 * r + j) + g * A.get! (14 * c + j)) % 5)
  return Array.ofFn (n := 49) fun t => (A.get! (14 * (t.val / 7) + 7 + t.val % 7)).toNat

@[expose] def congr7 (P S : Array Nat) : Array Nat :=
  let PS := mul7 P S
  Array.ofFn (n := 49) fun t =>
    let a := 7 * (t.val / 7)
    let b := 7 * (t.val % 7)
    (Nat.fold 7 (fun l _ acc => acc + PS[a + l]! * P[b + l]!) 0) % 5

@[expose] def encodeDigits (D : Nat → Nat) : ByteArray :=
  ⟨Array.ofFn (n := 276) fun q => code3 (D (3 * q.val)) (D (3 * q.val + 1)) (D (3 * q.val + 2))⟩

@[expose] def keyS (key : ByteArray) : Array Nat :=
  Array.ofFn (n := 49) fun t =>
    let c := (key.get! (259 + t.val / 3)).toNat
    if t.val % 3 = 0 then c % 5 else if t.val % 3 = 1 then c / 5 % 5 else c / 25 % 5

@[inline, expose] def keyFun (ds : Array ByteArray) (s : Array Nat) (p : Nat) : Nat :=
  if p < 777 then (ds[p / 111]!.get! (p % 111)).toNat else if p < 826 then s[p - 777]! else 0

@[expose] def pivots (ds : Array ByteArray) : Array Nat := Id.run do
  let mut ech : Array (Array Nat) := #[]
  let mut lead : Array Nat := #[]
  let mut piv : Array Nat := #[]
  for i in [0:111] do
    if piv.size < 7 then
      let mut v : Array Nat := Array.ofFn (n := 7) fun k => (ds[k.val]!.get! i).toNat
      for e in [0:ech.size] do
        let f := v[lead[e]!]!
        if f != 0 then
          let row := ech[e]!
          v := Array.ofFn (n := 7) fun k => (v[k.val]! + (5 - f) * row[k.val]!) % 5
      let mut l := 7
      for k in [0:7] do
        if l == 7 && v[k]! != 0 then l := k
      if l < 7 then
        let iv := inv5 v[l]!
        ech := ech.push (v.map fun x => x * iv % 5)
        lead := lead.push l
        piv := piv.push i
    else break
  return piv

@[expose] def rrefOK (ds : Array ByteArray) (piv : Array Nat) : Bool :=
  piv.size == 7 && ds.size == 7 && (ds.all fun d => d.size == 112) &&
    allIn 0 7 (fun m => piv[m]! < 111 && (m + 1 == 7 || piv[m]! < piv[m + 1]!)) &&
    allIn 0 7 (fun m => allIn 0 7 fun l =>
      (ds[m]!.get! piv[l]!).toNat == if l == m then 1 else 0) &&
    allIn 0 7 (fun m => allIn 0 piv[m]! fun j => (ds[m]!.get! j).toNat == 0)

@[expose] def actYs (T : Array W14) (key : ByteArray) : Array W14 :=
  Array.ofFn (n := 7) fun r => (rowProd T key r.val).red

@[expose] def pivMat (ys : Array W14) (piv : Array Nat) : Array Nat :=
  Array.ofFn (n := 49) fun t => ys[t.val % 7]!.lane piv[t.val / 7]! % 5

@[expose] def combine (ys : Array W14) (Pinv : Array Nat) : Array ByteArray :=
  Array.ofFn (n := 7) fun m =>
    (Nat.fold 7 (fun k _ acc => acc.add (W14.smul (UInt64.ofNat (Pinv[7 * k + m.val]! % 5)) ys[k]!))
      W14.zero).digits

@[expose] def actKey (T : Array W14) (key : ByteArray) : Option ByteArray :=
  let ys := actYs T key
  let piv := pivots (ys.map W14.digits)
  let P := pivMat ys piv
  let us := combine ys (inv7 P)
  if rrefOK us piv then some (encodeDigits (keyFun us (congr7 P (keyS key)))) else none

structure KOrbit where
  keys : Array ByteArray
  index : Std.HashMap ByteArray Nat
  alpha : Table
  beta : Table
  par : Table
  lab : Table
deriving Inhabited

@[expose] def bfs (TA TB : Array W14) (k₀ : ByteArray) (cap : Nat) : KOrbit := Id.run do
  let mut keys : Array ByteArray := #[k₀]
  let mut index : Std.HashMap ByteArray Nat := (∅ : Std.HashMap _ _).insert k₀ 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  for h in [0:cap] do
    if h < keys.size then
      let X := keys[h]!
      match actKey TA X with
      | none => alpha := alpha.push 0
      | some Y =>
        match index[Y]? with
        | some k => alpha := alpha.push (UInt32.ofNat k)
        | none =>
          index := index.insert Y keys.size
          alpha := alpha.push (UInt32.ofNat keys.size)
          keys := keys.push Y
          par := par.push (UInt32.ofNat h)
          lab := lab.push 1
      match actKey TB X with
      | none => beta := beta.push 0
      | some Y =>
        match index[Y]? with
        | some k => beta := beta.push (UInt32.ofNat k)
        | none =>
          index := index.insert Y keys.size
          beta := beta.push (UInt32.ofNat keys.size)
          keys := keys.push Y
          par := par.push (UInt32.ofNat h)
          lab := lab.push 2
    else break
  return ⟨keys, index, alpha, beta, par, lab⟩

@[expose] def imagesOf (TA TB : Array W14) (ks : Array ByteArray) :
    Array (Option ByteArray × Option ByteArray) :=
  ks.map fun k => (actKey TA k, actKey TB k)

@[expose] def bfsPar (TA TB : Array W14) (k₀ : ByteArray) (cap B nt : Nat) : KOrbit := Id.run do
  let mut keys : Array ByteArray := #[k₀]
  let mut index : Std.HashMap ByteArray Nat := (∅ : Std.HashMap _ _).insert k₀ 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  let mut h := 0
  for _ in [0:cap] do
    if h < keys.size && h < cap then
      let hi := min (min (h + B) keys.size) cap
      let batch := keys.extract h hi
      let chunk := (batch.size + nt - 1) / nt
      let tasks := (List.range nt).map fun c =>
        Task.spawn fun _ => imagesOf TA TB (batch.extract (c * chunk) ((c + 1) * chunk))
      let res := (tasks.map Task.get).toArray
      for i in [0:batch.size] do
        let (ya, yb) := res[i / chunk]![i % chunk]!
        match ya with
        | none => alpha := alpha.push 0
        | some Y =>
          match index[Y]? with
          | some k => alpha := alpha.push (UInt32.ofNat k)
          | none =>
            index := index.insert Y keys.size
            alpha := alpha.push (UInt32.ofNat keys.size)
            keys := keys.push Y
            par := par.push (UInt32.ofNat (h + i))
            lab := lab.push 1
        match yb with
        | none => beta := beta.push 0
        | some Y =>
          match index[Y]? with
          | some k => beta := beta.push (UInt32.ofNat k)
          | none =>
            index := index.insert Y keys.size
            beta := beta.push (UInt32.ofNat keys.size)
            keys := keys.push Y
            par := par.push (UInt32.ofNat (h + i))
            lab := lab.push 2
      h := hi
    else break
  return ⟨keys, index, alpha, beta, par, lab⟩

@[inline, expose] def orbitCheckAt (TA TB : Array W14) (O : KOrbit) (pos : ByteArray → Nat)
    (i : Nat) : Bool :=
  let n := O.keys.size
  let X := O.keys[i]!
  let a := ap O.alpha i
  let b := ap O.beta i
  pos X == i && a < n && b < n && actKey TA X == some O.keys[a]! &&
    actKey TB X == some O.keys[b]! &&
    (i == 0 || (ap O.par i < i &&
      ((ap O.lab i == 1 && ap O.alpha (ap O.par i) == i) ||
        (ap O.lab i == 2 && ap O.beta (ap O.par i) == i))))

@[expose] def orbitOK (TA TB : Array W14) (k₀ : ByteArray) (O : KOrbit) (chunks : Nat) : Bool :=
  0 < O.keys.size && O.keys.size < 2 ^ 30 && O.keys[0]! == k₀ &&
    parAll O.keys.size chunks (orbitCheckAt TA TB O (fun X => O.index.getD X O.keys.size))

end CFSG.Sporadic.Ly.Native
