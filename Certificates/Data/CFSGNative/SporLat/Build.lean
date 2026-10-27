module

public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] def buildOmega (act : Array Nat → Lab → Lab) (letters : Array (Array Nat)) (Δ : Lab)
    (cap : Nat) : OmegaData Lab × Bool := Id.run do
  let m := letters.size
  let mut lbl : Array Lab := #[Δ]
  let mut idx : Std.HashMap Lab Nat := (∅ : Std.HashMap Lab Nat).insert Δ 0
  let mut par : Array Nat := #[0]
  let mut via : Array Nat := #[0]
  let mut pn : Array (Array Nat) := Array.replicate m #[]
  let mut i := 0
  while i < lbl.size && lbl.size ≤ cap do
    let L := lbl[i]!
    for l in [0:m] do
      let M := act letters[l]! L
      match idx.get? M with
      | some j => pn := pn.modify l (fun a => a.push j)
      | none =>
        let j := lbl.size
        lbl := lbl.push M
        idx := idx.insert M j
        par := par.push i
        via := via.push l
        pn := pn.modify l (fun a => a.push j)
    i := i + 1
  return (⟨lbl, pn, par, via⟩, i == lbl.size)

@[expose] def labelIndex (lbl : Array Lab) : Std.HashMap Lab Nat := Id.run do
  let mut idx : Std.HashMap Lab Nat := {}
  for i in [0:lbl.size] do
    idx := idx.insert lbl[i]! i
  return idx

@[expose] def buildForest (act : Array Nat → Lab → Lab) (lbl : Array Lab)
    (letters : Array (Array Nat)) : ForestData := Id.run do
  let N := lbl.size
  let idx := labelIndex lbl
  let mut fpar : Array Nat := Array.replicate N 0
  let mut fl : Array Nat := Array.replicate N 0
  let mut fdep : Array Nat := Array.replicate N 0
  let mut froot : Array Nat := Array.replicate N 0
  let mut seen : Array Bool := Array.replicate N false
  let mut queue : Array Nat := Array.mkEmpty N
  for r in [0:N] do
    if !seen[r]! then
      seen := seen.set! r true
      froot := froot.set! r r
      let mut qi := queue.size
      queue := queue.push r
      while qi < queue.size do
        let x := queue[qi]!
        qi := qi + 1
        for l in [0:letters.size] do
          let y := (idx.get? (act letters[l]! lbl[x]!)).getD 0
          if !seen[y]! then
            seen := seen.set! y true
            fpar := fpar.set! y x
            fl := fl.set! y l
            fdep := fdep.set! y (fdep[x]! + 1)
            froot := froot.set! y r
            queue := queue.push y
  return ⟨fpar, fl, fdep, froot⟩

@[expose] def refSearch (act : Array Nat → Lab → Lab) (letters : Array (Array Nat)) (Δ : Lab)
    (idxMap : Std.HashMap Lab Nat) (F : ForestData) (isTop : Std.HashMap Nat Nat) :
    Option (List Nat × Nat × Nat) := Id.run do
  let m := letters.size
  let mut lbls : Array Lab := #[Δ]
  let mut seen : Std.HashSet Lab := (∅ : Std.HashSet Lab).insert Δ
  let mut par : Array Nat := #[0]
  let mut via : Array Nat := #[0]
  let mut i := 0
  while i < lbls.size do
    let L := lbls[i]!
    match idxMap.get? L with
    | some xi =>
      match isTop.get? F.froot[xi]! with
      | some pos =>
        let mut w : List Nat := []
        let mut node := i
        while node != 0 do
          w := w ++ [via[node]!]
          node := par[node]!
        return some (w, xi, pos)
      | none => pure ()
    | none => pure ()
    for l in [0:m] do
      let M := act letters[l]! L
      if !seen.contains M then
        seen := seen.insert M
        lbls := lbls.push M
        par := par.push i
        via := via.push l
    i := i + 1
  return none

@[expose] def mkAtom (root cls mode : Nat) (oc : OmegaData Lab) (refPos : Nat) (refWord : List Nat)
    (refIdx : Nat) : AtomData Lab := ⟨root, cls, mode, oc, refPos, refWord, refIdx⟩

@[expose] def mkJoin (j j' jj mode : Nat) (oj : OmegaData Lab) (refPos : Nat) (refWord : List Nat)
    (refIdx : Nat) : JoinData Lab := ⟨j, j', jj, mode, oj, refPos, refWord, refIdx⟩

@[expose] def labelsIn (o : OmegaData Lab) (s : Std.HashSet Lab) : Bool :=
  o.lbl.all fun x => s.contains x

structure MemState (Lab : Type) [BEq Lab] [Hashable Lab] where
  mw : Array (List (List Nat))
  mt : Array (List (Array Nat))
  Om : Array (OmegaData Lab)
  sets : Array (Std.HashSet Lab)

@[expose] def labelSet (o : OmegaData Lab) : Std.HashSet Lab :=
  o.lbl.foldl (fun s x => s.insert x) {}

@[expose] def findMember (st : MemState Lab) (o : OmegaData Lab) : Option Nat := Id.run do
  for j in [0:st.mw.size] do
    if st.Om[j]!.lbl.size == o.lbl.size && labelsIn o st.sets[j]! then
      return some j
  return none

@[expose] def gensInB (act : Array Nat → Lab → Lab) (Δ : Lab) (st : MemState Lab) (j jj : Nat) :
    Bool :=
  st.mt[j]!.all fun t => st.sets[jj]!.contains (act t Δ)

@[expose] def buildLat (act : Array Nat → Lab → Lab) (n : Nat) (ta tb : Array Nat) (Δ : Lab)
    (sTabs : List (Array Nat)) (cap : Nat) : LatData Lab := Id.run do
  let big := 1 <<< 60
  let (O, _) := buildOmega act #[ta, tb] Δ big
  let N := O.lbl.size
  let F := buildForest act O.lbl sTabs.toArray
  let idxMap := labelIndex O.lbl
  let rootsArr := (F.roots N).toArray
  let oS := (buildOmega act sTabs.toArray Δ cap).1
  let mut st : MemState Lab := ⟨#[[]], #[[]], #[oS], #[labelSet oS]⟩
  let mut atoms : Array (AtomData Lab) := #[]
  let mut pending : Array Nat := #[]
  for c in rootsArr do
    let w := O.pathWord c c
    let rc := wordTabA #[ta, tb] n w
    let (oc, complete) := buildOmega act (sTabs.toArray.push rc) Δ cap
    if complete then
      match findMember st oc with
      | some j => atoms := atoms.push (mkAtom c j 0 oc 0 [] 0)
      | none =>
        let j := st.mw.size
        st := ⟨st.mw.push [w], st.mt.push [rc], st.Om.push oc, st.sets.push (labelSet oc)⟩
        atoms := atoms.push (mkAtom c j 0 oc 0 [] 0)
    else
      pending := pending.push c
  let mut joinsAcc : Array (JoinData Lab) := #[]
  let mut done : Std.HashSet (Nat × Nat) := {}
  let mut changed := true
  while changed do
    changed := false
    let J0 := st.mw.size
    for j in [0:J0] do
      for j' in [j + 1:J0] do
        if !done.contains (j, j') then
          done := done.insert (j, j')
          if gensInB act Δ st j j' || gensInB act Δ st j' j then
            pure ()
          else
            let L := sTabs.toArray ++ st.mt[j]!.toArray ++ st.mt[j']!.toArray
            let (oj, complete) := buildOmega act L Δ cap
            if complete then
              match findMember st oj with
              | some jj => joinsAcc := joinsAcc.push (mkJoin j j' jj 0 oj 0 [] 0)
              | none =>
                let jj := st.mw.size
                st := ⟨st.mw.push (st.mw[j]! ++ st.mw[j']!), st.mt.push (st.mt[j]! ++ st.mt[j']!),
                  st.Om.push oj, st.sets.push (labelSet oj)⟩
                joinsAcc := joinsAcc.push (mkJoin j j' jj 0 oj 0 [] 0)
                changed := true
            else
              joinsAcc := joinsAcc.push (mkJoin j j' 0 2 default 0 [] 0)
  let J := st.mw.size
  let mut isTop : Std.HashMap Nat Nat := {}
  for k in [0:pending.size] do
    let c := pending[k]!
    let w := O.pathWord c c
    let rc := wordTabA #[ta, tb] n w
    let L := sTabs.toArray.push rc
    if isTop.isEmpty then
      let (oc, _) := buildOmega act L Δ big
      isTop := isTop.insert c atoms.size
      atoms := atoms.push (mkAtom c J 0 oc 0 [] 0)
    else
      match refSearch act L Δ idxMap F isTop with
      | some (word, xi, pos) =>
        isTop := isTop.insert c atoms.size
        atoms := atoms.push (mkAtom c J 1 default pos word xi)
      | none => atoms := atoms.push (mkAtom c (J + 1) 3 default 0 [] 0)
  let mut joins : List (JoinData Lab) := []
  for e in joinsAcc do
    if e.mode == 2 then
      let L := sTabs.toArray ++ st.mt[e.j]!.toArray ++ st.mt[e.j']!.toArray
      match refSearch act L Δ idxMap F isTop with
      | some (word, xi, pos) =>
        joins := mkJoin e.j e.j' J 1 default pos word xi :: joins
      | none => joins := e :: joins
    else
      joins := e :: joins
  return { O := O, F := F, sTabs := sTabs, mw := st.mw, mt := st.mt, Om := st.Om, atoms := atoms,
           joins := joins.reverse }

@[expose] def buildO2 (act : Array Nat → Lab → Lab) (D : LatData Lab) :
    Array (OmegaData (List Lab)) :=
  D.Om.map fun o => (buildOmega (tupAct act) D.sTabs.toArray o.lbl.toList (1 <<< 60)).1

end CFSG.QuasithinUnique.Ch1.SporLat
