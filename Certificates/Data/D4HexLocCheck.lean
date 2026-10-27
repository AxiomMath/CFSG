module

public import CFSG.LargeExtraspecial.S63CD4Inputs
public import Certificates.Data.D4HexLinkCheck
public import Certificates.Data.D4HexLocWords

public section

namespace CFSG.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Monster.B.Co2.Native

@[expose] def locComm (x y : Array ℕ) : Bool := mulR x y == mulR y x

@[expose] def locIsInv (x : Array ℕ) : Bool := mulR x x == oneR && !(x == oneR)

@[expose] def locStepArr (s : Bool × List ℕ) : Array ℕ × Array ℕ :=
  (wordR d4Gens s.2, wordR d4Gens s.2.reverse)

@[expose] def locSteps : Array (Array ℕ × Array ℕ) := (locStepWords.map locStepArr).toArray

@[expose] def locWordArr (w : List ℕ) : Array ℕ :=
  w.foldr (fun k acc => compA 819 permArrs[k]! acc) (idA 819)

@[expose] def locStepOK (s : Bool × List ℕ) : Bool :=
  s.2.all (fun k => decide (k < 8)) &&
    (if s.1 then (locWordArr s.2)[0]! == 0 else fixesLine0 (locWordArr s.2))

@[expose] def locForest (eT : EnumData) (roots : List ℕ) : List (ℕ × ℕ × ℕ) := Id.run do
  let n := eT.El.size
  let mut seen : Array Bool := Array.replicate n false
  let mut queue : Array ℕ := #[]
  for r in roots do
    if r < n then
      seen := seen.set! r true
      queue := queue.push r
  let mut out : Array (ℕ × ℕ × ℕ) := #[]
  let mut qi := 0
  while qi < queue.size do
    let p := queue[qi]!
    qi := qi + 1
    for s in [0:locSteps.size] do
      let y := conjI locSteps[s]!.1 locSteps[s]!.2 eT.El[p]!
      let j := eT.idx y
      if j < n && eT.El[j]! == y && !seen[j]! then
        seen := seen.set! j true
        queue := queue.push j
        out := out.push (j, p, s)
  return out.toList

@[expose] def locForestGo (eT : EnumData) : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | seen, (j, p, s) :: rest =>
      seen.contains p && decide (s < locSteps.size) && decide (j < eT.El.size) &&
        (conjI locSteps[s]!.1 locSteps[s]!.2 eT.El[p]! == eT.El[j]!) &&
        locForestGo eT (j :: seen) rest

@[expose] def locInvChain (eT : EnumData) : Bool :=
  let rz := eT.idx z0R
  let rt := eT.idx t0R
  decide (rz < eT.El.size) && eT.El[rz]! == z0R && decide (rt < eT.El.size) &&
    eT.El[rt]! == t0R &&
    (let F := locForest eT [rz, rt]
     locForestGo eT [rz, rt] F &&
       allLt eT.El.size fun i => !(locIsInv eT.El[i]!) || ([rz, rt] ++ F.map (·.1)).contains i)

@[expose] def locPairForest (eT : EnumData) (start : ℕ × ℕ) :
    List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ) := Id.run do
  let n := eT.El.size
  let mut seen : Std.HashSet (ℕ × ℕ) := {}
  seen := seen.insert start
  let mut queue : Array (ℕ × ℕ) := #[start]
  let mut out : Array ((ℕ × ℕ) × (ℕ × ℕ) × ℕ) := #[]
  let mut qi := 0
  while qi < queue.size do
    let p := queue[qi]!
    qi := qi + 1
    for s in [0:locSteps.size] do
      let ya := conjI locSteps[s]!.1 locSteps[s]!.2 eT.El[p.1]!
      let yb := conjI locSteps[s]!.1 locSteps[s]!.2 eT.El[p.2]!
      let ja := eT.idx ya
      let jb := eT.idx yb
      if ja < n && jb < n && eT.El[ja]! == ya && eT.El[jb]! == yb && !seen.contains (ja, jb) then
        seen := seen.insert (ja, jb)
        queue := queue.push (ja, jb)
        out := out.push ((ja, jb), p, s)
  return out.toList

@[expose] def locPairGo (eT : EnumData) : List (ℕ × ℕ) → List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ) → Bool
  | _, [] => true
  | seen, (j, p, s) :: rest =>
      seen.contains p && decide (s < locSteps.size) && decide (j.1 < eT.El.size) &&
        decide (j.2 < eT.El.size) &&
        (conjI locSteps[s]!.1 locSteps[s]!.2 eT.El[p.1]! == eT.El[j.1]!) &&
        (conjI locSteps[s]!.1 locSteps[s]!.2 eT.El[p.2]! == eT.El[j.2]!) &&
        locPairGo eT (j :: seen) rest

@[expose] def locPairChain (eT eQ : EnumData) (u0 : Array ℕ) : Bool :=
  let ia := eT.idx u0
  let ib := eT.idx t0R
  decide (ia < eT.El.size) && eT.El[ia]! == u0 && decide (ib < eT.El.size) &&
    eT.El[ib]! == t0R &&
    (let F := locPairForest eT (ia, ib)
     locPairGo eT [(ia, ib)] F &&
       ((ia, ib) :: F.map (·.1)).any fun p =>
         decide (p.1 < eT.El.size) && decide (p.2 < eT.El.size) && eT.El[p.1]! == z0R &&
           !memR eQ.El eQ.idx eT.El[p.2]!)

@[expose] def locTCheck (eT : EnumData) : Bool :=
  gensOK uGens && eT.ok uGens 4096 && locIsInv z0R && locIsInv t0R &&
    (allLt eT.El.size fun i =>
      !((List.range uGens.size).all fun k => locComm eT.El[i]! uGens[k]!) ||
        eT.El[i]! == oneR || eT.El[i]! == z0R) &&
    locInvChain eT

@[expose] def locVCheck (cz : ClassData) (eC : EnumData) (czC : ClassData) : Bool :=
  gensOK cGens && (List.range cGens.size).all (fun k => locComm cGens[k]! t0R) &&
    eC.ok cGens 3072 && cz.T[0]! == z0R &&
    locIsInv cz.T[1]! && locIsInv cz.T[5]! &&
    mulR z0R cz.T[1]! == cz.T[5]! && mulR cz.T[1]! z0R == cz.T[5]! &&
    mulR z0R cz.T[5]! == cz.T[1]! && mulR cz.T[5]! z0R == cz.T[1]! &&
    mulR cz.T[1]! cz.T[5]! == z0R && mulR cz.T[5]! cz.T[1]! == z0R &&
    locComm t0R z0R && locComm t0R cz.T[1]! && locComm t0R cz.T[5]! &&
    (List.range cGens.size).all (fun k => [z0R, cz.T[1]!, cz.T[5]!].all fun v =>
      let w := conjI cGens[k]! cGens[k]! v
      w == z0R || w == cz.T[1]! || w == cz.T[5]!) &&
    classTreeOK cGens z0R czC.T czC.P czC.K czC.idx &&
    memR czC.T czC.idx cz.T[1]! && memR czC.T czC.idx cz.T[5]! &&
    (List.range eC.El.size).any fun i =>
      locComm eC.El[i]! z0R && locComm eC.El[i]! cz.T[1]! && locComm eC.El[i]! cz.T[5]! &&
        (let s := mulR eC.El[i]! eC.El[i]!
         s == z0R || s == cz.T[1]! || s == cz.T[5]!)

@[expose] def locFusion (cz cu : ClassData) (eT eQ : EnumData) : Bool :=
  cWords.all (fun w => w.all (fun k => decide (k < 8)) && fixesLine0 (locWordArr w)) &&
    classTreeOK cGens (wordR d4Gens locU0Word) cu.T cu.P cu.K cu.idx &&
    (allLt 819 fun i => !(locComm cz.T[i]! t0R) || i == 0 || i == 1 || i == 5 ||
      memR cu.T cu.idx cz.T[i]!) &&
    memR eQ.El eQ.idx t0R && locPairChain eT eQ (wordR d4Gens locU0Word)

@[expose] def locPairWit (cz : ClassData) (eQ : EnumData) : ℕ × ℕ × ℕ := Id.run do
  for iv in [0:eQ.El.size] do
    let v := eQ.El[iv]!
    if locIsInv v && !memR cz.T cz.idx v then
      for ia in [0:eQ.El.size] do
        let a := eQ.El[ia]!
        if locComm a v then
          for ib in [0:eQ.El.size] do
            let b := eQ.El[ib]!
            if locComm b v && mulR a b == mulR z0R (mulR b a) then
              return (iv, ia, ib)
  return (0, 0, 0)

@[expose] def locPairWitOK (cz : ClassData) (eQ : EnumData) (w : ℕ × ℕ × ℕ) : Bool :=
  decide (w.1 < eQ.El.size) && decide (w.2.1 < eQ.El.size) && decide (w.2.2 < eQ.El.size) &&
    locIsInv eQ.El[w.1]! && !memR cz.T cz.idx eQ.El[w.1]! &&
    locComm eQ.El[w.2.1]! eQ.El[w.1]! && locComm eQ.El[w.2.2]! eQ.El[w.1]! &&
    mulR eQ.El[w.2.1]! eQ.El[w.2.2]! == mulR z0R (mulR eQ.El[w.2.2]! eQ.El[w.2.1]!)

@[expose] def locQCheck (cz : ClassData) (eT eQ : EnumData) : Bool :=
  gensOK qGens && eQ.ok qGens 512 && eT.invOK 4096 &&
    (allLt eQ.El.size fun i => (List.range qGens.size).all fun k =>
      mulR eQ.El[i]! qGens[k]! == mulR qGens[k]! eQ.El[i]! ||
        mulR eQ.El[i]! qGens[k]! == mulR z0R (mulR qGens[k]! eQ.El[i]!)) &&
    (allLt eQ.El.size fun i =>
      mulR eQ.El[i]! eQ.El[i]! == oneR || mulR eQ.El[i]! eQ.El[i]! == z0R) &&
    (allLt eQ.El.size fun i =>
      !((List.range qGens.size).all fun k => locComm eQ.El[i]! qGens[k]!) ||
        eQ.El[i]! == oneR || eQ.El[i]! == z0R) &&
    (List.range qGens.size).all (fun k => memR eT.El eT.idx qGens[k]!) &&
    (allLt eT.El.size fun i => (List.range uGens.size).all fun k =>
      memR eQ.El eQ.idx
        (mulR (mulR eT.El[i]! uGens[k]!) (mulR eT.El[eT.inv[i]!]! uGens[k]!))) &&
    (allLt eQ.El.size fun i =>
      !(locIsInv eQ.El[i]!) || memR cz.T cz.idx eQ.El[i]! ||
        (List.range uGens.size).any fun k =>
          let s := mulR (mulR uGens[k]! eQ.El[i]!) (mulR uGens[k]! eQ.El[i]!)
          !(s == oneR) && !(s == z0R)) &&
    locPairWitOK cz eQ (locPairWit cz eQ)

@[expose] def locCheckOn (cz : ClassData) (eT eC eQ : EnumData) (czC cu : ClassData) : Bool :=
  cz.ok d4Gens z0R 819 && locStepWords.all locStepOK && locTCheck eT && locVCheck cz eC czC &&
    locFusion cz cu eT eQ && locQCheck cz eT eQ

@[expose, irreducible] def locCz : ClassData := mkClass d4Gens z0R

@[expose, irreducible] def locET : EnumData := mkEnum uGens

@[expose, irreducible] def locEC : EnumData := mkEnum cGens

@[expose, irreducible] def locEQ : EnumData := mkEnum qGens

@[expose, irreducible] def locCzC : ClassData := mkClass cGens z0R

@[expose, irreducible] def locCu : ClassData := mkClass cGens (wordR d4Gens locU0Word)

@[expose] def locCheck : Bool := locCheckOn locCz locET locEC locEQ locCzC locCu

end CFSG.D4Hex
