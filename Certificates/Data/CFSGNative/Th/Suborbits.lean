module

public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Sporadic.Th.Native

structure Comps where
  lab : ByteArray
  ord : Table
  posOf : Table
  opl : Table
  reps : Array Nat

@[expose] def components (n : Nat) (g1 g2 : Table) : Comps := Id.run do
  let mut lab := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    lab := lab.push 255
  let mut ord : Table := Array.mkEmpty n
  let mut opl : Table := Array.mkEmpty n
  let mut posOf : Table := Array.replicate n 0
  let mut reps : Array Nat := #[]
  let mut scan := 0
  for h in [0:n] do
    if h == ord.size then
      for s in [scan:n] do
        if lab.get! s == 255 then
          lab := lab.set! s (UInt8.ofNat reps.size)
          posOf := posOf.set! s (UInt32.ofNat ord.size)
          ord := ord.push (UInt32.ofNat s)
          opl := opl.push 0
          reps := reps.push s
          scan := s + 1
          break
    if h < ord.size then
      let p := ap ord h
      let c := lab.get! p
      let a := ap g1 p
      if lab.get! a == 255 then
        lab := lab.set! a c
        posOf := posOf.set! a (UInt32.ofNat ord.size)
        ord := ord.push (UInt32.ofNat a)
        opl := opl.push (UInt32.ofNat (h ||| (1 <<< 30)))
      let b := ap g2 p
      if lab.get! b == 255 then
        lab := lab.set! b c
        posOf := posOf.set! b (UInt32.ofNat ord.size)
        ord := ord.push (UInt32.ofNat b)
        opl := opl.push (UInt32.ofNat (h ||| (2 <<< 30)))
  return ⟨lab, ord, posOf, opl, reps⟩

@[inline, expose] def Comps.labelOf (c : Comps) (p : Nat) : Nat := (c.lab.get! p).toNat

@[inline, expose] def compCheckAt (n : Nat) (c : Comps) (g1 g2 : Table) (t : Nat) : Bool :=
  let p := ap c.ord t
  let r := (c.opl[t]!).toNat
  p < n && ap c.posOf p == t &&
    c.labelOf (ap g1 t) == c.labelOf t && c.labelOf (ap g2 t) == c.labelOf t &&
    c.labelOf t < c.reps.size &&
    (if treeLab r == 0 then c.reps[c.labelOf p]! == p
     else
      let par := treePar r
      par < t && c.labelOf (ap c.ord par) == c.labelOf p &&
        ((treeLab r == 1 && ap g1 (ap c.ord par) == p) ||
          (treeLab r == 2 && ap g2 (ap c.ord par) == p)))

@[expose] def compOK (n : Nat) (c : Comps) (g1 g2 : Table) : Bool :=
  allIn 0 n (compCheckAt n c g1 g2)

@[expose] def countLabels (n k : Nat) (c : Comps) : Array Nat :=
  Nat.fold n (fun p _ acc => acc.modify (c.labelOf p) (· + 1)) (Array.replicate k 0)

end CFSG.Sporadic.Th.Native
