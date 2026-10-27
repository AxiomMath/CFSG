module

public import Certificates.Data.CFSGNative.NineAll.Check

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall CFSG.ReflExt CFSG.NineAll

set_option compiler.extract_closed false

@[expose] def e6Edge (i j : Nat) : Bool :=
  (i == 0 && j == 2) || (i == 2 && j == 0) || (i == 1 && j == 3) || (i == 3 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 4) || (i == 4 && j == 3) ||
  (i == 4 && j == 5) || (i == 5 && j == 4)

@[expose] def verifyWE6 (P : Pt) (c : WWit) : Bool :=
  c.sigma.length == 6 &&
  c.sigma.all (fun s => P.wordOK s.1 && decide (s.2 < P.gens.length)) &&
  (let S := c.sigma.map fun s => P.sigmaVecs s.1 s.2
   S.all (fun cb => P.dotv cb.2 cb.1 == 2 % P.p) &&
   (List.range 6).all (fun i => (List.range 6).all fun j =>
     i == j ||
       (let a := P.dotv (S.getD i ([], [])).2 (S.getD j ([], [])).1
        let b := P.dotv (S.getD j ([], [])).2 (S.getD i ([], [])).1
        if e6Edge i j then (a * b) % P.p == 1 else a == 0 && b == 0)) &&
   c.expr.length == P.gens.length &&
   ((c.expr.zip P.gens).all fun (w, r) =>
      w.all (fun i => decide (i < 6)) &&
        (List.range P.D).all fun j =>
          P.vecEq (P.sigmaWord S w (P.unit j)) (P.applyRefl r (P.unit j)))) &&
  verifyO P c.chain 51839

@[expose] def invModD (p a : Nat) : Nat := ((List.range p).find? fun m => (a * m) % p == 1).getD 1

@[expose] def canonCB (P : Pt) (cb : Vec × Vec) : Vec × Vec :=
  match (List.range P.D).find? (fun i => P.ent cb.1 i != 0) with
  | some i =>
    let l := P.ent cb.1 i
    let li := invModD P.p l
    ((List.range P.D).map fun j => (P.ent cb.1 j * li) % P.p,
     (List.range P.D).map fun j => (P.ent cb.2 j * l) % P.p)
  | none => cb

@[expose] def keyCB (P : Pt) (cb : Vec × Vec) : Nat × Nat :=
  let n := canonCB P cb
  (P.code n.1, P.code n.2)

@[expose] def reflClosD (P : Pt) (cap : Nat) : Option (List ((Word × Nat) × (Vec × Vec))) :=
  let m := P.gens.length
  let rec go (fuel : Nat) (queue : List (Word × Nat)) (seen : List (Nat × Nat))
      (acc : List ((Word × Nat) × (Vec × Vec))) : Option (List ((Word × Nat) × (Vec × Vec))) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match queue with
      | [] => some acc.reverse
      | (w, k) :: rest =>
        let cb := P.sigmaVecs w k
        let key := keyCB P cb
        if seen.contains key then go fuel rest seen acc
        else if cap ≤ acc.length then none
        else go fuel (rest ++ (List.range m).map fun j => (j :: w, k)) (key :: seen) (((w, k), cb) :: acc)
  go ((cap + 2) * (m + 1) + 10) ((List.range m).map fun k => (([] : Word), k)) [] []

@[expose] def e6SysD (P : Pt) (R : List (Vec × Vec)) : Option (List Nat) :=
  let Ra := R.toArray
  let pa (i j : Nat) : Nat := P.dotv (Ra.getD i ([], [])).2 (Ra.getD j ([], [])).1
  let adj (i j : Nat) : Bool := i != j && (pa i j * pa j i) % P.p == 1
  let orth (i j : Nat) : Bool := pa i j == 0 && pa j i == 0
  let idx := List.range R.length
  idx.findSome? fun s3 =>
    (idx.filter fun s2 => adj s2 s3).findSome? fun s2 =>
      (idx.filter fun s1 => adj s1 s3 && orth s1 s2).findSome? fun s1 =>
        (idx.filter fun s4 => adj s4 s3 && orth s4 s1 && orth s4 s2).findSome? fun s4 =>
          (idx.filter fun s0 => adj s0 s2 && orth s0 s1 && orth s0 s3 && orth s0 s4).findSome? fun s0 =>
            (idx.filter fun s5 => adj s5 s4 && orth s5 s0 && orth s5 s1 && orth s5 s2 && orth s5 s3).head?.map
              fun s5 => [s0, s1, s2, s3, s4, s5]

@[expose] def e6ExprD (P : Pt) (S : List (Vec × Vec)) (cap : Nat) : Option (List Word) :=
  let conjBy (cb : Vec × Vec) (j : Nat) : Vec × Vec :=
    let sj := S.getD j ([], [])
    (P.sigmaApply sj cb.1, (List.range P.D).map fun m => P.dotv cb.2 (P.sigmaApply sj (P.unit m)))
  let rec go (fuel : Nat) (queue : List (Word × (Vec × Vec))) (seen : List (Nat × Nat))
      (acc : List (Word × (Nat × Nat))) : List (Word × (Nat × Nat)) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match queue with
      | [] => acc
      | (u, cb) :: rest =>
        let key := keyCB P cb
        if seen.contains key then go fuel rest seen acc
        else go fuel (rest ++ (List.range 6).map fun j => (j :: u ++ [j], conjBy cb j)) (key :: seen)
          ((u, key) :: acc)
  let table := go ((cap + 2) * 7 + 10) ((List.range 6).map fun i => ([i], S.getD i ([], []))) [] []
  P.gens.mapM fun r =>
    let key := keyCB P (r.h, r.f)
    (table.find? fun e => e.2 == key).map (·.1)

@[expose] def findWE6 (P : Pt) : Option WWit := do
  let R ← reflClosD P 64
  let sys ← e6SysD P (R.map (·.2))
  let sigma := sys.map fun i => (R.getD i (([], 0), ([], []))).1
  let expr ← e6ExprD P (sigma.map fun s => P.sigmaVecs s.1 s.2) 64
  let chain ← orderWit (withBound P 51839)
  pure ⟨5, sigma, expr, chain⟩

@[expose] def classifyD (P0 : Pt) (cand : List Refl) (t : Refl) : Option NRep :=
  if centOK P0 t then some ⟨t, .cent, [], [], []⟩
  else
    let P1 := withExtra P0 [t]
    match findBad P1 with
    | some w => some ⟨t, .w w, [], [], []⟩
    | none =>
      match findWE6 P1 with
      | some c =>
        if wfCheck P1 && verifyWE6 P1 c then
          match buildStage2N P0 cand t with
          | some (roots, reps2, orb2) => some ⟨t, .w (.weyl c), roots, reps2, orb2⟩
          | none => none
        else none
      | none => none

@[expose] def buildD (P0 : Pt) (Bstab : Nat) : Option NTables :=
  let roots := rootsOf P0 20000
  let rootsR := roots.map (·.r)
  let cand := candList P0 rootsR
  let fixing := cand.filter fun c => P0.dotv c.f P0.x == 0 && !(rootsR.any (reqb c))
  let ot0 := orbitTable P0 P0.gens.length 20000 fixing
  let reps0? := ot0.1.mapM fun c =>
    (findBad (withBound (withExtra P0 [c]) Bstab)).map fun w => (⟨c, w⟩ : Rep0)
  let ot1 := orbitTable P0 P0.gens.length 20000 (movingOf P0 cand)
  let reps? := ot1.1.mapM fun t => classifyD P0 cand t
  match reps0?, reps? with
  | some reps0, some reps => some ⟨roots, ot0.2, reps0, ot1.2, reps⟩
  | _, _ => none

@[expose] def verifyRepD (P0 : Pt) (cand : List Refl) (rp : NRep) : Bool :=
  wfR P0 rp.r && P0.dotv rp.r.f P0.x != 0 &&
  (match rp.kind with
   | .w w =>
     (match w with
      | .weyl c =>
        wfCheck (withExtra P0 [rp.r]) && verifyWE6 (withExtra P0 [rp.r]) c && verifyStage2N P0 cand rp
      | .kernel _ => false
      | .transv _ => verify (withExtra P0 [rp.r]) w
      | .order _ => verify (withExtra P0 [rp.r]) w)
   | .cent => centOK P0 rp.r)

@[expose] def centEntryOK (P0 : Pt) (T : NTables) (e : OEnt) : Bool :=
  match T.reps[e.j]? with
  | some rp =>
    (match rp.kind with
     | .cent => reqb e.e rp.r || reqb e.e (negR P0 rp.r)
     | .w _ => true)
  | none => false

@[expose] def verifyAllD (P0 : Pt) (Bstab : Nat) (T : NTables) : Bool :=
  wfCheck P0 && vFixN P0 && vRootsN P0 T &&
  (let cand := candOfN P0 T
   vCover0 P0 T cand && T.orb0.all (entry0OK P0 T) && T.reps0.all (rep0OK P0 Bstab) &&
   vCover1 P0 T cand && T.orb1.all (entry1OK P0 T) && T.reps.all (verifyRepD P0 cand) &&
   T.orb1.all (centEntryOK P0 T))

@[expose] def checkFrameD (P0 : Pt) (Bstab : Nat) : Bool :=
  match buildD P0 Bstab with
  | some T => verifyAllD P0 Bstab T
  | none => false

end CFSG.DepFrame

end
