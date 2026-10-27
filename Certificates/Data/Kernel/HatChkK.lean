module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatChk
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Std.Data.HashMap

public section

namespace CFSG.KC.HatChkK

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Quasithin.H13.Ch4.HatChk

@[expose] def memL (n : ℕ) (ps : List ℕ) (P : Array (Array ℕ)) (t : Array ℕ) : Bool :=
  P.toList.any fun p => keyA n ps p == keyA n ps t && eqA n t p

@[expose] def coverOKL (n m : ℕ) (ps : List ℕ) (P₁ P₂ : Array (Array ℕ)) (cls : Array ℕ) : Bool :=
  let mem := P₁.map fun t => memL n ps P₂ t
  let idx := (List.range P₁.size).filter fun i => mem[i]!
  idx.all (fun i => decide (cls[i]! < m)) &&
    idx.all fun i => idx.all fun j =>
      i == j || cls[i]! != cls[j]! || !cmA n P₁[i]! P₁[j]!

@[expose] def greedyCoverL (n : ℕ) (ps : List ℕ) (P₁ P₂ : Array (Array ℕ)) : Array ℕ := Id.run do
  let mut cls : Array ℕ := Array.replicate P₁.size 0
  let mut classes : Array (Array ℕ) := #[]
  for i in [0:P₁.size] do
    if memL n ps P₂ P₁[i]! then
      let mut placed := false
      for k in [0:classes.size] do
        if !placed && (classes[k]!).all (fun j => !cmA n P₁[i]! P₁[j]!) then
          classes := classes.set! k ((classes[k]!).push i)
          cls := cls.set! i k
          placed := true
      if !placed then
        cls := cls.set! i classes.size
        classes := classes.push #[i]
  return cls

@[expose] def gIn (cm : ℕ → ℕ → Bool) (i : ℕ) (st : Array ℕ × Array (Array ℕ) × Bool) (k : ℕ) :
    Array ℕ × Array (Array ℕ) × Bool :=
  if !st.2.2 && (st.2.1[k]!).toList.all (fun j => !cm i j) then
    (st.1.set! i k, st.2.1.set! k ((st.2.1[k]!).push i), true)
  else st

@[expose] def gOut (mem : ℕ → Bool) (cm : ℕ → ℕ → Bool) (st : Array ℕ × Array (Array ℕ))
    (i : ℕ) : Array ℕ × Array (Array ℕ) :=
  if mem i then
    let r := (List.range' 0 st.2.size).foldl (gIn cm i) (st.1, st.2, false)
    if !r.2.2 then (r.1.set! i r.2.1.size, r.2.1.push #[i]) else (r.1, r.2.1)
  else st

@[expose] def greedyF (N : ℕ) (mem : ℕ → Bool) (cm : ℕ → ℕ → Bool) : Array ℕ :=
  ((List.range' 0 N).foldl (gOut mem cm) (Array.replicate N 0, #[])).1

@[expose] def coverF (N m : ℕ) (mem : ℕ → Bool) (cls : ℕ → ℕ) (cm : ℕ → ℕ → Bool) : Bool :=
  let idx := (List.range N).filter mem
  idx.all (fun i => decide (cls i < m)) &&
    idx.all fun i => idx.all fun j => i == j || cls i != cls j || !cm i j

section Packed

open CFSG.KC.Enum (pg pcomp)
open CFSG.KS (mask)

@[expose] noncomputable def fpfK (n w p : ℕ) : Bool :=
  (List.range n).all fun i => !Nat.beq (pg w (mask w) p i) i

@[expose] noncomputable def cmK (n w p q : ℕ) : Bool :=
  Nat.beq (pcomp n w (mask w) p q) (pcomp n w (mask w) q p)

@[expose] noncomputable def fpfPairK (n w ng : ℕ) (G : ℕ → ℕ) (r t : ℕ) : Bool :=
  !((List.range ng).all (fun k => cmK n w (G k) t) && fpfK n w t && !Nat.beq t r) ||
    !fpfK n w (pcomp n w (mask w) r t)

end Packed

@[expose] def base24 : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

end CFSG.KC.HatChkK

end
