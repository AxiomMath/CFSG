module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def findO (P : Pt) (b : Nat) : Option OWit :=
  let fzo_lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  let fzo_pick (s : Nat) (n : Nat) : Nat := (s / 4294967296) % n
  let rec fzo_rndVecGo (P : Pt) (n : Nat) (s : Nat) (acc : List Nat) : Vec × Nat :=
    match n with
    | 0 => (acc.reverse, s)
    | n + 1 =>
        let s' := fzo_lcg s
        fzo_rndVecGo P n s' (fzo_pick s' P.p :: acc)
  let fzo_rndVec (P : Pt) (s : Nat) : Vec × Nat := fzo_rndVecGo P P.D s []
  let fzo_matId (P : Pt) : List Vec := (List.range P.D).map fun a => P.unit a
  let fzo_reflMat (P : Pt) (i : Nat) : List Vec :=
    let r := P.gens.getD i ⟨[], []⟩
    (List.range P.D).map fun a =>
      (List.range P.D).map fun b =>
        ((if a = b then 1 else 0) + (P.p - (r.h.getD a 0 * r.f.getD b 0) % P.p)) % P.p
  let fzo_matApply (P : Pt) (M : List Vec) (v : Vec) : Vec :=
    (List.range P.D).map fun a => P.dotv (M.getD a []) v
  let fzo_matMul (P : Pt) (A B : List Vec) : List Vec :=
    (List.range P.D).map fun a =>
      (List.range P.D).map fun b =>
        ((List.range P.D).map (fun k => (A.getD a []).getD k 0 * (B.getD k []).getD b 0)).foldl (· + ·) 0 % P.p
  let fzo_moved (P : Pt) (curM : Array (List Vec)) (v : Vec) : Bool :=
    curM.toList.any fun M => (P.vecEq (fzo_matApply P M v) v) == false
  let rec fzo_chooseBaseRnd (P : Pt) (curM : Array (List Vec)) (n : Nat) (s : Nat) : Option (Vec × Nat) :=
    match n with
    | 0 => none
    | n + 1 =>
        let (v, s') := fzo_rndVec P s
        if fzo_moved P curM v then some (v, s') else fzo_chooseBaseRnd P curM n s'
  let fzo_chooseBase (P : Pt) (curM : Array (List Vec)) (seed : Nat) : Option (Vec × Nat) :=
    match (List.range P.D).find? (fun i => fzo_moved P curM (P.unit i)) with
    | some i => some (P.unit i, seed)
    | none => fzo_chooseBaseRnd P curM 30 seed
  let fzo_bfs (P : Pt) (curW : Array Word) (curM : Array (List Vec)) (curMI : Array (List Vec)) (v0 : Vec) :
      Array (Vec × Nat × Nat) × Array Word × Array (List Vec) × Array (List Vec) × Array Nat :=
    Id.run do
      let mut index : Array Nat := (List.replicate (P.p ^ P.D) 0).toArray
      let mut tree : Array (Vec × Nat × Nat) := #[]
      let mut transW : Array Word := #[]
      let mut transM : Array (List Vec) := #[]
      let mut transMI : Array (List Vec) := #[]
      let mut queue : Array Vec := #[v0]
      index := index.set! (P.code v0) 1
      tree := tree.push (v0, 0, 0)
      transW := transW.push []
      transM := transM.push (fzo_matId P)
      transMI := transMI.push (fzo_matId P)
      let mut head := 0
      while head < queue.size do
        let v := queue[head]!
        let pidx := head
        let wW := transW[pidx]!
        let wM := transM[pidx]!
        let wMI := transMI[pidx]!
        for k in List.range curM.size do
          let w := fzo_matApply P curM[k]! v
          let c := P.code w
          if index[c]! == 0 then
            index := index.set! c (tree.size + 1)
            tree := tree.push (w, pidx, k)
            transW := transW.push (curW[k]! ++ wW)
            transM := transM.push (fzo_matMul P curM[k]! wM)
            transMI := transMI.push (fzo_matMul P wMI curMI[k]!)
            queue := queue.push w
        head := head + 1
      return (tree, transW, transM, transMI, index)
  let rec fzo_schreier (P : Pt) (curW : Array Word) (curM : Array (List Vec)) (curMI : Array (List Vec))
      (tree : Array (Vec × Nat × Nat)) (transW : Array Word)
      (transM : Array (List Vec)) (transMI : Array (List Vec)) (index : Array Nat)
      (n : Nat) (s : Nat) (accW : Array Word) (accM : Array (List Vec)) (accMI : Array (List Vec)) :
      Array Word × Array (List Vec) × Array (List Vec) × Nat :=
    match n with
    | 0 => (accW, accM, accMI, s)
    | n + 1 =>
        let s1 := fzo_lcg s
        let a := fzo_pick s1 tree.size
        let s2 := fzo_lcg s1
        let gi := fzo_pick s2 curM.size
        let gM := curM[gi]!
        let w2 := fzo_matApply P gM tree[a]!.1
        let j := index[P.code w2]! - 1
        let t2W := transW[j]!
        let t2MI := transMI[j]!
        let t1W := transW[a]!
        let t1M := transM[a]!
        let sW := t2W.reverse ++ curW[gi]! ++ t1W
        let sM := fzo_matMul P (fzo_matMul P t2MI gM) t1M
        let sMI := fzo_matMul P (fzo_matMul P transMI[a]! curMI[gi]!) transM[j]!
        fzo_schreier P curW curM curMI tree transW transM transMI index n s2
          (accW.push sW) (accM.push sM) (accMI.push sMI)
  let rec fzo_chainAux (curW : Array Word) (curM : Array (List Vec)) (curMI : Array (List Vec))
      (samples : Nat) (fuel : Nat) (prod : Nat) (seed : Nat) (acc : List Level) : Option (List Level) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        if prod > b then some acc.reverse
        else
          match fzo_chooseBase P curM seed with
          | none => none
          | some (base, seed1) =>
              let (tree, transW, transM, transMI, index) := fzo_bfs P curW curM curMI base
              let level : Level := { base := base, strong := curW.toList, tree := tree.toList }
              let prod' := prod * tree.size
              if prod' > b then some (level :: acc).reverse
              else
                let (schW, schM, schMI, seed2) :=
                  fzo_schreier P curW curM curMI tree transW transM transMI index samples seed1 #[] #[] #[]
                fzo_chainAux schW schM schMI samples fuel prod' seed2 (level :: acc)
  let n := P.gens.length
  let fzo_seedOf : Nat :=
    (P.gens.foldl (fun acc r => acc + r.f.foldl (· + ·) 0 + r.h.foldl (· + ·) 0 + 1) 0
      + P.x.foldl (· + ·) 0 + P.D + P.p) % 1000003
  let curW : Array Word := ((List.range n).map (fun i => [i])).toArray
  let curM : Array (List Vec) := ((List.range n).map (fun i => fzo_reflMat P i)).toArray
  let s0 := 12345 + fzo_seedOf
  match fzo_chainAux curW curM curM 40 64 1 s0 [] with
  | some ls => some ⟨ls⟩
  | none =>
    match fzo_chainAux curW curM curM 40 64 1 (s0 + 2) [] with
    | some ls => some ⟨ls⟩
    | none => none

end CFSG.TwoNodeSmall
