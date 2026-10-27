module

public import Certificates.Data.CFSGNative.ReflExt.Core
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchPos
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchPosO

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def rootsOf (P : Pt) (fuel : Nat) : List Root :=
  let n := P.gens.length
  let init : List Root := (List.range n).flatMap fun k =>
    match P.gens[k]? with
    | some g => [⟨g, [k]⟩, ⟨negR P g, [k]⟩]
    | none => []
  let rec go : Nat → List Root → Nat → List Root
    | 0, seen, _ => seen
    | fuel + 1, seen, k =>
      match seen[k]? with
      | none => seen
      | some cur =>
        let new := (List.range n).foldl (fun acc i =>
          let r' := conjR P i cur.r
          if acc.any (fun s => reqb s.r r') then acc else acc ++ [⟨r', i :: (cur.w ++ [i])⟩]) seen
        go fuel new (k + 1)
  go fuel init 0

@[expose] def orbitOf (P : Pt) (m fuel : Nat) (start : Refl) : List (Refl × Word) :=
  let rec go : Nat → List (Refl × Word) → Nat → List (Refl × Word)
    | 0, seen, _ => seen
    | fuel + 1, seen, k =>
      match seen[k]? with
      | none => seen
      | some cur =>
        let new := (List.range m).foldl (fun acc i =>
          let r' := conjR P i cur.1
          if acc.any (fun s => reqb s.1 r') then acc else acc ++ [(r', cur.2 ++ [i])]) seen
        go fuel new (k + 1)
  let orb := go fuel [(start, [])] 0
  orb.foldl (fun acc s =>
    let n := negR P s.1
    if acc.any (fun t => reqb t.1 n) then acc else acc ++ [(n, s.2)]) orb

@[expose] def orbitTable (P : Pt) (m fuel : Nat) (cs : List Refl) : List Refl × List OEnt :=
  cs.foldl (fun (st : List Refl × List OEnt) c =>
    if st.2.any (fun e => reqb e.e c) then st
    else
      let j := st.1.length
      let orb := orbitOf P m fuel c
      (st.1 ++ [c], st.2 ++ orb.map fun s => ⟨s.1, s.2, j⟩)) ([], [])

@[expose] def orderWit (P : Pt) : Option OWit :=
  (List.range 9).findSome? fun k =>
    match findOCap { P with x := P.x ++ List.replicate k 1 } P.bound 1000000000 40 with
    | some o => if verifyO P o P.bound then some o else none
    | none => none

@[expose] def classifyRep (P0 : Pt) (r : Refl) : Option RKind :=
  match findPos ⟨withExtra P0 [r], 0⟩ with
  | some (.order o) => some (.bad o)
  | some (.weyl c) => some (.good c)
  | _ => none

@[expose] def buildStage2 (P0 : Pt) (cand : List Refl) (r : Refl) : List Root × List Rep2 × List OEnt × Bool :=
  let Pj := withExtra P0 [r]
  let roots := rootsOf Pj 20000
  let rd := roots.map (·.r)
  let ext := cand.filter fun c => !(rd.any (reqb c)) && !(asymAny Pj rd c)
  let ot := orbitTable Pj Pj.gens.length 20000 ext
  let bad := ot.1.mapIdx fun j q => (j, q, orderWit (withExtra P0 [r, q]))
  let reps2 := (bad.filterMap fun b => match b.2.2 with | some o => some (b.1, (⟨b.2.1, o⟩ : Rep2)) | none => none)
  let keep := reps2.map (·.1)
  let ent := ot.2.filterMap fun e =>
    match keep.idxOf? e.j with
    | some j' => some (⟨e.e, e.w, j'⟩ : OEnt)
    | none => none
  (roots, reps2.map (·.2), ent, decide (keep.length = ot.1.length))

@[expose] def buildTables (P0 : Pt) : Option Tables :=
  let roots := rootsOf P0 20000
  let cand := candList P0 (roots.map (·.r))
  let ot := orbitTable P0 P0.gens.length 20000 (movingOf P0 cand)
  let reps? := ot.1.mapM fun r =>
    match classifyRep P0 r with
    | some (.bad o) => some (⟨r, .bad o, true, [], [], []⟩ : Rep)
    | some (.good c) =>
      let s2 := buildStage2 P0 cand r
      some (⟨r, .good c, s2.2.2.2, s2.1, s2.2.1, s2.2.2.1⟩ : Rep)
    | none => none
  match reps? with
  | some reps => some ⟨roots, ot.2, reps⟩
  | none => none

@[expose] def Rep.isGoodMax (rp : Rep) : Bool :=
  match rp.kind with
  | .good _ => rp.maximal
  | .bad _ => false

@[expose] def s2Roots (P0 : Pt) (rp : Rep) : Bool :=
  rp.roots.all fun ρ => wfR P0 ρ.r && realizes (withExtra P0 [rp.r]) ρ.w ρ.r

@[expose] def s2Reps (P0 : Pt) (rp : Rep) : Bool :=
  rp.reps2.all fun q => wfR P0 q.r && wfCheck (withExtra P0 [rp.r, q.r]) &&
    verifyO (withExtra P0 [rp.r, q.r]) q.o P0.bound

@[expose] def s2Orb (P0 : Pt) (rp : Rep) : Bool :=
  rp.orb2.all fun x => wfR P0 x.e && decide (x.j < rp.reps2.length) &&
    (match rp.reps2[x.j]? with
     | some q => realizes (withExtra P0 [rp.r, x.e]) (x.w ++ [P0.gens.length + 1] ++ x.w.reverse) q.r
     | none => false)

@[expose] def s2Cand (P0 : Pt) (T : Tables) (rp : Rep) (c : Refl) : Bool :=
  (rp.roots.map (·.r)).any (reqb c) || asymAny (withExtra P0 [rp.r]) (rp.roots.map (·.r)) c ||
    rp.orb2.any (fun x => reqb x.e c) ||
    (!rp.maximal && T.orb1.any fun e => reqb e.e c &&
      (match T.reps[e.j]? with | some rq => rq.isGoodMax | none => false))

@[expose] def verifyStage2 (P0 : Pt) (T : Tables) (cand : List Refl) (rp : Rep) : Bool :=
  s2Roots P0 rp && s2Reps P0 rp && s2Orb P0 rp && cand.all (s2Cand P0 T rp)

@[expose] def verifyRep (P0 : Pt) (T : Tables) (cand : List Refl) (rp : Rep) : Bool :=
  wfR P0 rp.r && wfCheck (withExtra P0 [rp.r]) &&
  (match rp.kind with
   | .bad o => verifyO (withExtra P0 [rp.r]) o P0.bound
   | .good c => verifyWPos (withExtra P0 [rp.r]) c && verifyStage2 P0 T cand rp)

@[expose] def candOf (P0 : Pt) (T : Tables) : List Refl := candList P0 (T.roots.map (·.r))

@[expose] def vRoots (P0 : Pt) (T : Tables) : Bool :=
  T.roots.all fun ρ => wfR P0 ρ.r && realizes P0 ρ.w ρ.r && P0.dotv ρ.r.f P0.x == 0

@[expose] def vCover (P0 : Pt) (T : Tables) (cand : List Refl) : Bool :=
  (movingOf P0 cand).all fun c => T.orb1.any fun e => reqb e.e c

@[expose] def entryOK (P0 : Pt) (T : Tables) (e : OEnt) : Bool :=
  wfR P0 e.e && decide (e.j < T.reps.length) &&
    (match T.reps[e.j]? with
     | some rp => realizes (withExtra P0 [e.e]) (e.w ++ [P0.gens.length] ++ e.w.reverse) rp.r
     | none => false)

@[expose] def verifyAll (P0 : Pt) (T : Tables) : Bool :=
  wfCheck P0 && vRoots P0 T &&
  (let cand := candOf P0 T
   vCover P0 T cand && T.orb1.all (entryOK P0 T) && T.reps.all (verifyRep P0 T cand))

@[expose] def checkFrame (P0 : Pt) : Bool :=
  match buildTables P0 with
  | some T => verifyAll P0 T
  | none => false

@[expose, reducible] def unitV (D k : Nat) : Vec := (List.range D).map fun j => if j = k then 1 else 0

@[expose, reducible] def mkFrame (p n D : Nat) (row : Nat → Vec) (s : Nat) (xl : Vec) (bound : Nat) : Pt :=
  { p := p, D := D, nFrame := n,
    gens := (List.range n).map fun i =>
      ⟨row i ++ (if D = n + 1 then [if i = 0 then s else 0] else []), unitV D i⟩,
    x := xl ++ (if D = n + 1 then [0] else []),
    bound := bound }



end CFSG.ReflExt

end
