module

public import Certificates.Data.CFSGNative.J4.Orbit

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

structure Labels where
  lab : ByteArray
  par : ByteArray
  dep : ByteArray
  reps : Array Nat
deriving Inhabited

@[inline, expose] def bitGet (b : ByteArray) (q : Nat) : Bool :=
  ((b.get! (q >>> 3)).toNat >>> (q &&& 7)) &&& 1 == 1

@[inline, expose] def bitSet (b : ByteArray) (q : Nat) : ByteArray :=
  b.set! (q >>> 3) (b.get! (q >>> 3) ||| UInt8.ofNat (1 <<< (q &&& 7)))

@[expose] def orbitRecords (n : Nat) (t1 t2 t3 : ByteArray) (reps : Array Nat) (cap : Nat) :
    ByteArray := Id.run do
  let mut seen := zeros ((n + 7) / 8)
  let mut rs := ByteArray.emptyWithCapacity (8 * cap)
  let mut h := 0
  for r in reps do
    seen := bitSet seen r
    rs := pushU32 (pushU32 rs r) 0
    for _ in [0:n] do
      if h < rs.size / 8 then
        let p := rdU32 rs (2 * h)
        h := h + 1
        for l in [1:4] do
          let q := rdU32 (letter3 t1 t2 t3 l) p
          if !bitGet seen q then
            seen := bitSet seen q
            rs := pushU32 (pushU32 rs q) (p ||| (l <<< 30))
      else break
  return rs

@[expose] def mergeLabels (n : Nat) (reps : Array Nat) (groups : Array (Array Nat))
    (recs : Array ByteArray) : Labels := Id.run do
  let mut lab : ByteArray := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    lab := lab.push 255
  let mut dep := zeros n
  let mut par := zeros (4 * n)
  for g in [0:recs.size] do
    let R := recs[g]!
    let G := groups[g]!
    let mut cur := 255
    let mut c := 0
    for k in [0:R.size / 8] do
      let q := rdU32 R (2 * k)
      let pl := rdU32 R (2 * k + 1)
      if pl == 0 then
        cur := G[c]?.getD 255
        c := c + 1
        lab := lab.set! q (UInt8.ofNat cur)
      else
        lab := lab.set! q (UInt8.ofNat cur)
        par := wrU32 par q pl
        dep := dep.set! q (dep.get! (pl &&& 0x3FFFFFFF) + 1)
  return ⟨lab, par, dep, reps⟩

@[expose] def labelPar (n : Nat) (t1 t2 t3 : ByteArray) (reps sizes : Array Nat)
    (groups : Array (Array Nat)) : Labels :=
  let tasks := groups.map fun G => Task.spawn fun _ =>
    orbitRecords n t1 t2 t3 (G.map fun c => reps[c]!) (G.foldl (fun s c => s + sizes[c]!) 0)
  mergeLabels n reps groups (tasks.map Task.get)

@[inline, expose] def Labels.labelOf (L : Labels) (p : Nat) : Nat := (L.lab.get! p).toNat

@[inline, expose] def labelAt (n : Nat) (t1 t2 t3 : ByteArray) (L : Labels) (p : Nat) : Bool :=
  L.labelOf p < L.reps.size &&
    if depOf L.dep p == 0 then L.reps[L.labelOf p]! == p else
      let p0 := parOf L.par p
      let l := labOf L.par p
      p0 < n && 1 ≤ l && l ≤ 3 && rdU32 (letter3 t1 t2 t3 l) p0 == p &&
        L.labelOf p0 == L.labelOf p && depOf L.dep p0 + 1 == depOf L.dep p

@[expose] def labelOK (n : Nat) (t1 t2 t3 : ByteArray) (L : Labels) (chunks : Nat) : Bool :=
  parAllS n chunks (labelAt n t1 t2 t3 L)

@[expose] def countLab (n k : Nat) (L : Labels) : Array Nat :=
  Nat.fold n (fun p _ acc => acc.modify (L.labelOf p) (· + 1)) (Array.replicate k 0)

end CFSG.Sporadic.J4.Native
