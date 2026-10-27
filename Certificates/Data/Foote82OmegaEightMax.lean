module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.CGT.Foote82.OmegaEight

open CFSG.EvenSmallLie.OmegaEightMinus

@[expose] def stabTree (_ : Unit := ()) :
    Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let gs : Array (Array ℕ) := (stabIdx.map fun j => omegaS[j]!).toArray
  let mut par : Array ℕ := Array.replicate 136 0
  let mut lab : Array ℕ := Array.replicate 136 0
  let mut dep : Array ℕ := Array.replicate 136 1000
  let mut col : Array ℕ := Array.replicate 136 0
  let mut roots : Array ℕ := #[]
  for c in [1:3] do
    let mut r := 0
    for p in [1:136] do
      if r == 0 && col[p]! == 0 then r := p
    if r != 0 then
      roots := roots.push r
      dep := dep.set! r 0
      col := col.set! r c
      let mut queue : Array ℕ := #[r]
      let mut h := 0
      for _ in [0:136] do
        if h < queue.size then
          let x := queue[h]!
          h := h + 1
          for l in [0:gs.size] do
            let y := (gs[l]!)[x]!
            if y < 136 && y != 0 && col[y]! == 0 then
              col := col.set! y c
              dep := dep.set! y (dep[x]! + 1)
              par := par.set! y x
              lab := lab.set! y l
              queue := queue.push y
  return (par, lab, dep, col, roots)

@[expose] def stabTreeOK (par lab dep col : Array ℕ) (r₁ r₂ : ℕ) : Bool :=
  col[0]! == 0 && decide (1 ≤ r₁) && decide (r₁ < 136) && decide (1 ≤ r₂) && decide (r₂ < 136) &&
    col[r₁]! == 1 && col[r₂]! == 2 &&
    (List.range 135).all (fun i =>
      (col[i + 1]! == 1 || col[i + 1]! == 2) &&
        (if dep[i + 1]! == 0 then i + 1 == r₁ || i + 1 == r₂ else
          decide (par[i + 1]! < 136) && decide (lab[i + 1]! < stabIdx.length) &&
            decide (dep[par[i + 1]!]! < dep[i + 1]!) && col[par[i + 1]!]! == col[i + 1]! &&
            (omegaS[stabIdx.getD lab[i + 1]! 0]!)[par[i + 1]!]! == i + 1)) &&
    (Finset.univ.filter fun p : Fin 136 => col[(p : ℕ)]! = 1).card == 63 &&
    (Finset.univ.filter fun p : Fin 136 => col[(p : ℕ)]! = 2).card == 72

@[expose] def stabTreeCheck (_ : Unit := ()) : Bool :=
  let T := stabTree ()
  stabTreeOK T.1 T.2.1 T.2.2.1 T.2.2.2.1 (T.2.2.2.2.getD 0 0) (T.2.2.2.2.getD 1 0)

end CFSG.CGT.Foote82.OmegaEight
