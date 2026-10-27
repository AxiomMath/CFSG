module

public import Certificates.Data.CFSGNative.Timmesfeld.PcFus

public section

namespace Timmesfeld.Mon7

open Timmesfeld.PcReg Timmesfeld.PcFus CFSG.HardMathSupport.Foote.E27

set_option compiler.extract_closed false

@[expose] def pw7 : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0]]

@[expose] def cw7 : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0], #[0, 1, 1, 0, 0, 3], #[0, 0, 1, 1, 0, 4], #[0, 0, 0, 1, 1, 5], #[0, 0, 0, 0, 1, 2], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 1, 0, 0, 6], #[0, 0, 0, 1, 0, 1], #[0, 0, 0, 0, 1, 1], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 1, 0, 6], #[0, 0, 0, 0, 1, 0], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 1, 0], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0]]

@[expose] def cwR7 : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0], #[0, 1, 6, 1, 6, 4], #[0, 0, 1, 6, 1, 6], #[0, 0, 0, 1, 6, 4], #[0, 0, 0, 0, 1, 5], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 1, 0, 0, 1], #[0, 0, 0, 1, 0, 6], #[0, 0, 0, 0, 1, 6], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 1, 0, 1], #[0, 0, 0, 0, 1, 0], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 1, 0], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0]]

@[expose] def alphaVecs : Array (Array (Array Nat)) := #[#[#[5, 2, 3, 0, 4, 1], #[0, 6, 0, 0, 0, 0], #[0, 0, 2, 4, 4, 5], #[0, 0, 0, 3, 5, 3], #[0, 0, 0, 0, 1, 1], #[0, 0, 0, 0, 0, 6]], #[#[5, 1, 0, 0, 6, 5], #[0, 2, 3, 6, 6, 6], #[0, 0, 3, 0, 3, 6], #[0, 0, 0, 1, 2, 2], #[0, 0, 0, 0, 5, 4], #[0, 0, 0, 0, 0, 3]]]

@[expose] def orbVec : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 6, 0], #[0, 0, 0, 6, 0, 0], #[0, 0, 6, 0, 3, 0], #[0, 0, 6, 0, 2, 0], #[0, 0, 6, 0, 5, 0], #[0, 5, 0, 0, 0, 0], #[0, 5, 0, 0, 2, 0], #[0, 5, 0, 0, 6, 0], #[0, 5, 0, 0, 4, 0], #[0, 5, 0, 6, 1, 0], #[0, 5, 0, 6, 2, 0], #[0, 5, 0, 6, 6, 0], #[0, 5, 0, 6, 4, 0], #[0, 5, 0, 4, 1, 0], #[0, 5, 0, 4, 3, 0], #[0, 5, 0, 4, 6, 0], #[0, 5, 0, 4, 4, 0], #[6, 3, 0, 0, 0, 0], #[6, 2, 0, 0, 0, 0], #[6, 2, 0, 0, 0, 3], #[6, 2, 0, 0, 0, 2]]

@[expose] def wordOfVec (n : Nat) (v : Array Nat) : List Nat :=
  (List.range n).flatMap fun k => List.replicate v[k]! k

@[expose] def orbWord : Array (List Nat) := orbVec.map (wordOfVec 6)

@[expose] def genIdx (p n : Nat) (pw cwR : Array (Array Nat)) (j : Nat) : Nat :=
  ((leftTables p n pw cwR)[j]!)[0]!

@[expose] def prodIdx (p n : Nat) (pw cwR : Array (Array Nat)) (l : List Nat) : Nat :=
  l.foldr (fun j a => tabMul (parTree p n) (leftTables p n pw cwR) (genIdx p n pw cwR j) a) 0

@[expose] def autIdxT : Thunk (Array (Array Nat)) := .mk fun _ =>
  alphaVecs.map fun A => A.map fun v => prodIdx 7 6 pw7 cwR7 (wordOfVec 6 v)

@[expose] def targetEltsT : Thunk (Array Nat) := .mk fun _ => orbWord.map fun w => prodIdx 7 6 pw7 cwR7 w

@[expose] def targetClsT : Thunk (Array Nat) := .mk fun _ =>
  targetEltsT.get.map fun i => (pcLab 7 6 pw7 cwR7).lab[i]!

@[expose] def nMovesT : Thunk Nat := .mk fun _ => autIdxT.get.size + 5

@[expose] noncomputable abbrev autIdx : Array (Array Nat) := autIdxT.get
@[expose] noncomputable abbrev targetElts : Array Nat := targetEltsT.get
@[expose] noncomputable abbrev targetCls : Array Nat := targetClsT.get
@[expose] noncomputable abbrev nMoves : Nat := nMovesT.get

@[expose] def fusRoute (lab rep : Array Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat)) :
    Array (Nat × Nat) × Array Nat := Id.run do
  let K := rep.size
  let big := K + 1
  let mut depth : Array Nat := Array.replicate K big
  let mut route : Array (Nat × Nat) := Array.replicate K (0, 0)
  for t in targetClsT.get do
    if t < K then depth := depth.set! t 0
  for r in [1:K + 1] do
    let mut newD := depth
    let mut newR := route
    let mut changed := false
    for c in [0:K] do
      if depth[c]! == big then
        let mut found := false
        for mv in [0:nMovesT.get] do
          if !found then
            let i' := moveIdx 7 P L autIdxT.get #[] rep[c]! mv
            if i' < 7 ^ 6 && i' != 0 then
              let c' := lab[i']!
              if c' < K && depth[c']! < r then
                found := true
                newD := newD.set! c r
                newR := newR.set! c (mv, c')
                changed := true
    depth := newD
    route := newR
    if !changed then break
  return (route, depth)

@[expose] def mon7OK (_ : Unit := ()) : Bool :=
  let L := leftTables 7 6 pw7 cwR7
  let P := parTree 7 6
  let lb := pcLab 7 6 pw7 cwR7
  let rd := fusRoute lb.lab lb.rep P L
  pcFullOK 7 6 pw7 cw7 cwR7 &&
    fusOK 7 6 P L lb.lab lb.rep autIdxT.get #[] targetClsT.get rd.1 rd.2 &&
    decide (targetEltsT.get.size = orbWord.size) &&
    targetEltsT.get.all (fun i => decide (i < 7 ^ 6) && i != 0 && tabPowIdx P L i 7 == 0) &&
    (orbWord.all fun w => w.all fun j => decide (j < 6))

end Timmesfeld.Mon7
