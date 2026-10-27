module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley

@[expose] def tcEnt (a : Array ℤ) (i : ℕ) : ℤ := a.getD i 0

@[expose] def tcDot (n : ℕ) (a b : Array ℤ) : ℤ :=
  (List.range n).foldl (fun s i => s + tcEnt a i * tcEnt b i) 0

@[expose] def tcEqMod (p n : ℕ) (a b : Array ℤ) : Bool :=
  (List.range n).all fun i => (tcEnt a i - tcEnt b i) % (p : ℤ) == 0

@[expose] def tcIsZero (p n : ℕ) (a : Array ℤ) : Bool :=
  (List.range n).all fun i => tcEnt a i % (p : ℤ) == 0

@[expose] def tcLinComb (n : ℕ) (cs : List ℤ) (vs : List (Array ℤ)) : Array ℤ :=
  Array.ofFn (n := n) fun j => (List.zipWith (fun c v => c * tcEnt v j) cs vs).sum

@[expose] def tcLeadFrom (p : ℕ) (a : Array ℤ) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tcEnt a s % (p : ℤ) != 0 then s else tcLeadFrom p a (s + 1) k

@[expose] def tcLead (p n : ℕ) (a : Array ℤ) : ℕ := tcLeadFrom p a 0 n

@[expose] def tcInv (p : ℕ) (a : ℤ) : ℤ := (a % (p : ℤ)) ^ (p - 2) % (p : ℤ)

@[expose] def tcLetter (p n : ℕ) (A : Array (Array ℤ)) (θ c : Array ℤ) (l : ℕ) (f : Array ℤ) :
    Array ℤ :=
  if l < n then
    Array.ofFn (n := n) fun j => (tcEnt f j - tcEnt (A.getD l #[]) j * tcEnt f l) % (p : ℤ)
  else
    let t := tcDot n θ f
    Array.ofFn (n := n) fun j => (tcEnt f j - tcEnt c j * t) % (p : ℤ)

@[expose] def tcWord (p n : ℕ) (A : Array (Array ℤ)) (θ c : Array ℤ) (w : List ℕ) (f : Array ℤ) :
    Array ℤ :=
  w.foldl (fun g l => tcLetter p n A θ c l g) f

@[expose] def tcGenWord (p n : ℕ) (A : Array (Array ℤ)) (θ c : Array ℤ)
    (gens : Array (List ℕ)) (w : List ℕ) (f : Array ℤ) : Array ℤ :=
  w.foldl (fun g gi => tcWord p n A θ c (gens.getD gi []) g) f

@[expose] def tcCartan (τ : Tag) (_ : Unit := ()) : Array (Array ℤ) :=
  Array.ofFn fun i : Fin τ.rank => Array.ofFn fun j : Fin τ.rank => τ.cartan i j

@[expose] def tcGramMat (τ : Tag) (_ : Unit := ()) : Array (Array ℤ) :=
  Array.ofFn fun i : Fin τ.rank => Array.ofFn fun j : Fin τ.rank => τ.symmetrizedCartan i j

@[expose] def tcTheta : Tag → Array ℤ
  | .G2 => #[2, 3]
  | .F4 => #[2, 3, 4, 2]
  | .D4 => #[1, 1, 2, 1]
  | .E6 => #[1, 2, 2, 3, 2, 1]
  | .E7 => #[2, 2, 3, 4, 3, 2, 1]
  | .E8 => #[2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def tcCoTheta : Tag → Array ℤ
  | .G2 => #[1, 0]
  | .F4 => #[1, 0, 0, 0]
  | .D4 => #[0, 0, 1, 0]
  | .E6 => #[0, 1, 0, 0, 0, 0]
  | .E7 => #[1, 0, 0, 0, 0, 0, 0]
  | .E8 => #[0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def tcRoots (τ : Tag) (_ : Unit := ()) : Array (Array ℤ) :=
  ((List.range τ.rootCertificate.roots.length).map fun k =>
    Array.ofFn (τ.rootCertificate.root k)).toArray

@[expose] def tcGramTab (τ : Tag) (_ : Unit := ()) : Array (Array ℤ) :=
  let B := tcGramMat τ ()
  let R := tcRoots τ ()
  let BR := R.map fun a => Array.ofFn (n := τ.rank) fun i => tcDot τ.rank (B.getD i #[]) a
  BR.map fun ba => R.map fun b => tcDot τ.rank ba b

@[expose] def tcCoTab (τ : Tag) (_ : Unit := ()) : Array (Array ℤ) :=
  let B := tcGramMat τ ()
  (tcRoots τ ()).map fun a =>
    let Ba := Array.ofFn (n := τ.rank) fun i => tcDot τ.rank (B.getD i #[]) a
    let g := tcDot τ.rank Ba a
    Ba.map fun x => 2 * x / g

@[expose] def tcAlcAux : List ℕ → ℕ → List (List ℕ)
  | [], _ => [[]]
  | t :: ts, b => (List.range (b / t + 1)).flatMap fun v => (tcAlcAux ts (b - t * v)).map (v :: ·)

@[expose] def tcAlcove (τ : Tag) (p : ℕ) : List (Array ℤ) :=
  (tcAlcAux ((tcTheta τ).toList.map Int.toNat) p).map fun l =>
    (l.map (fun v : ℕ => (v : ℤ))).toArray

@[expose] def tcBfsClass (G : Array (Array ℤ)) (phi : List ℕ) (i : ℕ) : List ℕ :=
  let rec go : ℕ → List ℕ → ℕ → List ℕ
    | 0, C, _ => C
    | fuel + 1, C, k =>
      match C[k]? with
      | none => C
      | some x =>
        go fuel (C ++ phi.filter fun y => !C.contains y && tcEnt (G.getD x #[]) y != 0) (k + 1)
  go 2000 [i] 0

@[expose] def tcClasses (G : Array (Array ℤ)) (phi : List ℕ) : List (List ℕ) :=
  phi.foldl (fun acc i => if acc.any (·.contains i) then acc else acc ++ [tcBfsClass G phi i]) []

@[expose] def tcClassOK (G : Array (Array ℤ)) (phi : List ℕ) (C : List ℕ) : Bool :=
  !C.isEmpty && C.all (fun x => phi.contains x) &&
    (List.range C.length).all (fun j => j == 0 ||
      (List.range j).any fun i => tcEnt (G.getD (C.getD i 0) #[]) (C.getD j 0) != 0) &&
    C.all fun x => phi.all fun y => tcEnt (G.getD x #[]) y == 0 || C.contains y

@[expose] def tcClassesOK (G : Array (Array ℤ)) (phi : List ℕ) (cls : List (List ℕ)) : Bool :=
  cls.all (tcClassOK G phi) && phi.all fun i => cls.any (·.contains i)

def tcRref (p n : ℕ) (rows : List (Array ℤ)) : Array (Array ℤ) × List ℕ := Id.run do
  let mut M : Array (Array ℤ) :=
    (rows.map fun r => Array.ofFn (n := n) fun j => tcEnt r j % (p : ℤ)).toArray
  let mut piv : List ℕ := []
  let mut r := 0
  for c in List.range n do
    match (List.range' r (M.size - r)).find? fun i => tcEnt M[i]! c != 0 with
    | none => pure ()
    | some i =>
      let tmp := M[r]!
      M := (M.set! r M[i]!).set! i tmp
      let inv := tcInv p (tcEnt M[r]! c)
      let rowr : Array ℤ := Array.ofFn (n := n) fun j => tcEnt M[r]! j * inv % (p : ℤ)
      M := M.set! r rowr
      for k in List.range M.size do
        if k != r then
          let f := tcEnt M[k]! c
          if f != 0 then
            let rowk : Array ℤ :=
              Array.ofFn (n := n) fun j => (tcEnt M[k]! j - f * tcEnt rowr j) % (p : ℤ)
            M := M.set! k rowk
      piv := piv ++ [c]
      r := r + 1
  return (M, piv)

@[expose] def tcKernel (p n : ℕ) (rows : List (Array ℤ)) : List (Array ℤ × ℕ) :=
  let rr := tcRref p n rows
  (List.range n).filterMap fun f =>
    if rr.2.contains f then none
    else
      some (Array.ofFn (n := n) fun j =>
        if j.val == f then 1
        else match rr.2.findIdx? (· == j.val) with
          | some t => (-(tcEnt (rr.1.getD t #[]) f)) % (p : ℤ)
          | none => 0, f)

structure TcEch where
  vec : Array ℤ
  piv : ℕ
  coef : Array ℤ

def tcEchelon (p n : ℕ) (gens : List (Array ℤ)) : List TcEch :=
  let m := gens.length
  ((gens.zipIdx).foldl (fun (rows : List TcEch) gi =>
    let v0 : Array ℤ := Array.ofFn (n := n) fun j => tcEnt gi.1 j % (p : ℤ)
    let c0 : Array ℤ := Array.ofFn (n := m) fun j => if j.val == gi.2 then 1 else 0
    let vc := rows.foldl (fun (vc : Array ℤ × Array ℤ) r =>
      let f := tcEnt vc.1 r.piv
      if f == 0 then vc
      else (Array.ofFn (n := n) fun j => (tcEnt vc.1 j - f * tcEnt r.vec j) % (p : ℤ),
            Array.ofFn (n := m) fun j => (tcEnt vc.2 j - f * tcEnt r.coef j) % (p : ℤ))) (v0, c0)
    if tcIsZero p n vc.1 then rows
    else
      let pv := tcLead p n vc.1
      let inv := tcInv p (tcEnt vc.1 pv)
      rows ++ [⟨Array.ofFn (n := n) fun j => tcEnt vc.1 j * inv % (p : ℤ), pv,
        Array.ofFn (n := m) fun j => tcEnt vc.2 j * inv % (p : ℤ)⟩]) [])

@[expose] def tcKerOK (p n : ℕ) (rows : List (Array ℤ)) (vs : List (Array ℤ × ℕ)) : Bool :=
  vs.all (fun v => rows.all fun r => tcDot n r v.1 % (p : ℤ) == 0) &&
    (List.range vs.length).all fun j =>
      decide ((vs.getD j (#[], 0)).2 < n) &&
        tcEnt (vs.getD j (#[], 0)).1 (vs.getD j (#[], 0)).2 % (p : ℤ) != 0 &&
        (List.range j).all fun i =>
          tcEnt (vs.getD j (#[], 0)).1 (vs.getD i (#[], 0)).2 % (p : ℤ) == 0

@[expose] def tcEchOK (p n : ℕ) (gens : List (Array ℤ)) (rows : List TcEch) : Bool :=
  rows.all (fun r => tcEqMod p n r.vec (tcLinComb n r.coef.toList gens)) &&
    (List.range rows.length).all fun j =>
      decide ((rows.getD j ⟨#[], 0, #[]⟩).piv < n) &&
        tcEnt (rows.getD j ⟨#[], 0, #[]⟩).vec (rows.getD j ⟨#[], 0, #[]⟩).piv % (p : ℤ) != 0 &&
        (List.range j).all fun i =>
          tcEnt (rows.getD j ⟨#[], 0, #[]⟩).vec (rows.getD i ⟨#[], 0, #[]⟩).piv % (p : ℤ) == 0

@[expose] def tcEncFrom (p : ℕ) (a : Array ℤ) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (tcEnt a s % (p : ℤ)).toNat + p * tcEncFrom p a (s + 1) k

@[expose] def tcEnc (p n : ℕ) (a : Array ℤ) : ℕ := tcEncFrom p a 0 n

@[expose] def tcDec (p n m : ℕ) : Array ℤ :=
  Array.ofFn (n := n) fun i => ((m / p ^ i.val % p : ℕ) : ℤ)

@[expose] def tcCombo (p n : ℕ) (basis : List (Array ℤ)) (t : ℕ) : Array ℤ :=
  (tcLinComb n ((List.range basis.length).map fun j => ((t / p ^ j % p : ℕ) : ℤ)) basis).map
    (· % (p : ℤ))

@[expose] def tcCombos (p n : ℕ) (basis : List (Array ℤ)) : List (Array ℤ) :=
  ((List.range (p ^ basis.length)).map (tcCombo p n basis)).filter fun s => !tcIsZero p n s

@[expose] def tcNormalized (p n : ℕ) (d : Array ℤ) : Bool :=
  tcEnt d (tcLead p n d) % (p : ℤ) == 1

structure TcEnv where
  p : ℕ
  n : ℕ
  A : Array (Array ℤ)
  θ : Array ℤ
  c : Array ℤ
  R : Array (Array ℤ)
  G : Array (Array ℤ)
  Cor : Array (Array ℤ)
  L : List (Array ℤ)
  gens : Array (List ℕ)

@[expose] def tcEnv (τ : Tag) (p : ℕ) (L : List (Array ℤ)) (gens : Array (List ℕ)) : TcEnv :=
  ⟨p, τ.rank, tcCartan τ (), tcTheta τ, tcCoTheta τ, tcRoots τ (), tcGramTab τ (),
    tcCoTab τ (), L, gens⟩

@[expose] def tcInV (E : TcEnv) (v : Array ℤ) : Bool :=
  E.L.all fun l => tcDot E.n l v % (E.p : ℤ) == 0

@[expose] def tcDimV (E : TcEnv) : ℕ := E.n - E.L.length

@[expose] def tcLOK (E : TcEnv) : Bool :=
  tcEchOK E.p E.n E.L (tcEchelon E.p E.n E.L) && (tcEchelon E.p E.n E.L).length == E.L.length

@[expose] def tcSimpleGens (n : ℕ) : Array (List ℕ) := ((List.range n).map fun i => [i]).toArray

@[expose] def tcGenApply (E : TcEnv) (w : List ℕ) (f : Array ℤ) : Array ℤ :=
  tcGenWord E.p E.n E.A E.θ E.c E.gens w f

structure TcOrb where
  word : Array (List ℕ)
  rep : Array ℕ

instance : Inhabited TcOrb := ⟨⟨#[], #[]⟩⟩

def tcOrbBuild (E : TcEnv) : TcOrb := Id.run do
  let M := E.p ^ E.n
  let mut word : Array (List ℕ) := Array.replicate M []
  let mut rep : Array ℕ := Array.replicate M M
  for s in List.range M do
    if rep[s]! == M && tcInV E (tcDec E.p E.n s) then
      rep := rep.set! s s
      let mut queue : Array ℕ := #[s]
      let mut k := 0
      while k < queue.size do
        let v := queue[k]!
        let fv := tcDec E.p E.n v
        for gi in List.range E.gens.size do
          let w := tcEnc E.p E.n (tcGenApply E [gi] fv)
          if rep[w]! == M then
            rep := rep.set! w s
            word := word.set! w (gi :: word[v]!)
            queue := queue.push w
        k := k + 1
  return ⟨word, rep⟩

@[expose] def tcOrbOK (E : TcEnv) (T : TcOrb) : Bool :=
  (List.range (E.p ^ E.n)).all fun idx =>
    !tcInV E (tcDec E.p E.n idx) ||
      tcEqMod E.p E.n (tcGenApply E (T.word.getD idx []) (tcDec E.p E.n idx))
        (tcDec E.p E.n (T.rep.getD idx 0))

@[expose] def tcOrbVerified (E : TcEnv) : Option TcOrb :=
  let T := tcOrbBuild E
  if tcOrbOK E T then some T else none

def tcDescent (p n : ℕ) (A : Array (Array ℤ)) (θ c : Array ℤ) (lam : Array ℤ) :
    Array ℤ × List ℕ :=
  let rec go : ℕ → Array ℤ → List ℕ → Array ℤ × List ℕ
    | 0, lam, w => (lam, w.reverse)
    | fuel + 1, lam, w =>
      match (List.range n).find? fun i => tcEnt lam i < 0 with
      | some i =>
        go fuel (Array.ofFn (n := n) fun j => tcEnt lam j - tcEnt (A.getD i #[]) j * tcEnt lam i)
          (i :: w)
      | none =>
        let t := tcDot n θ lam
        if t > (p : ℤ) then
          go fuel (Array.ofFn (n := n) fun j => tcEnt lam j - (t - p) * tcEnt c j) (n :: w)
        else (lam, w.reverse)
  go 100000 lam []

def tcFindCover (E : TcEnv) (targets : List (Array ℤ)) (basis : List (Array ℤ)) :
    List (ℕ × List ℕ) :=
  let total := E.p ^ basis.length
  let rec go : ℕ → ℕ → List (Array ℤ) → List (ℕ × List ℕ) → List (ℕ × List ℕ)
    | 0, _, _, acc => acc
    | fuel + 1, t, remaining, acc =>
      if remaining.isEmpty || total ≤ t then acc
      else
        let s := tcCombo E.p E.n basis t
        if tcIsZero E.p E.n s then go fuel (t + 1) remaining acc
        else
          let r := tcDescent E.p E.n E.A E.θ E.c s
          if remaining.contains r.1 then
            go fuel (t + 1) (remaining.filter (· != r.1)) ((t, r.2) :: acc)
          else go fuel (t + 1) remaining acc
  go total 1 targets []

@[expose] def tcCoverOK (E : TcEnv) (alc : List (Array ℤ)) (basis : List (Array ℤ)) : Bool :=
  let targets := alc.filter fun m => !tcIsZero E.p E.n m
  let trips := tcFindCover E targets basis
  targets.all fun m => trips.any fun t =>
    let s := tcCombo E.p E.n basis t.1
    !tcIsZero E.p E.n s && tcEqMod E.p E.n (tcWord E.p E.n E.A E.θ E.c t.2 s) m

@[expose] def tcPlaneBad (E : TcEnv) (d1 d2 : Array ℤ) : Bool :=
  let phi := (List.range E.R.size).filter fun r =>
    tcDot E.n (E.R.getD r #[]) d1 % (E.p : ℤ) == 0 &&
      tcDot E.n (E.R.getD r #[]) d2 % (E.p : ℤ) == 0
  phi.isEmpty ||
    (let rows := E.L ++ phi.map fun r => E.R.getD r #[]
     let ker := tcKernel E.p E.n rows
     4 ≤ ker.length && tcKerOK E.p E.n rows (ker.take 4))

@[expose] def tcComb2 (n : ℕ) (a b : ℕ) (d1 d2 : Array ℤ) : Array ℤ :=
  Array.ofFn (n := n) fun j => (a : ℤ) * tcEnt d1 j + (b : ℤ) * tcEnt d2 j

@[expose] def tcPlaneIn (p n : ℕ) (NT : Array Bool) (d1 d2 : Array ℤ) : Bool :=
  (List.range p).all (fun c => !tcEqMod p n d2 (tcComb2 n c 0 d1 d2)) &&
    (List.range p).all fun a => (List.range p).all fun b =>
      (a == 0 && b == 0) || NT.getD (tcEnc p n (tcComb2 n a b d1 d2)) false

@[expose] def tcHitReps (E : TcEnv) (T : TcOrb) (basis : List (Array ℤ)) : List ℕ :=
  ((tcCombos E.p E.n basis).map fun s => T.rep.getD (tcEnc E.p E.n s) 0).dedup

@[expose] def tcNTable (E : TcEnv) (T : TcOrb) (basis : List (Array ℤ)) : Array Bool :=
  let hit := tcHitReps E T basis
  Array.ofFn (n := E.p ^ E.n) fun idx =>
    let v := tcDec E.p E.n idx.val
    tcInV E v && !tcIsZero E.p E.n v && !hit.contains (T.rep.getD idx.val 0)

@[expose] def tcPlaneOK (E : TcEnv) (T : TcOrb) (basis : List (Array ℤ)) : Bool :=
  let NT := tcNTable E T basis
  let Nl := (List.range (E.p ^ E.n)).filter fun i => NT.getD i false
  Nl.all fun i1 =>
    let d1 := tcDec E.p E.n i1
    !tcNormalized E.p E.n d1 ||
      Nl.all fun i2 =>
        let d2 := tcDec E.p E.n i2
        !tcPlaneIn E.p E.n NT d1 d2 || tcPlaneBad E d1 d2

@[expose] def tcCaseOK (E : TcEnv) (OT : Thunk (Option TcOrb)) (alc : List (Array ℤ))
    (cover : Bool) (b : Array ℤ) (O : List ℕ) (ag : List (Array ℤ)) : Bool :=
  let rows := E.L ++ O.map fun i => E.R.getD i #[]
  let ker := tcKernel E.p E.n rows
  if 3 ≤ ker.length then tcKerOK E.p E.n rows (ker.take 3)
  else
    let gens := b :: ag
    let ech := tcEchelon E.p E.n gens
    tcEchOK E.p E.n gens ech && ech.all (fun r => tcInV E r.vec) && ag.all (tcInV E) &&
      (tcDimV E ≤ ech.length + 1 ||
        (cover && tcCoverOK E alc (ech.map (·.vec))) ||
        match OT.get with
        | none => false
        | some T => tcPlaneOK E T (ech.map (·.vec)))

@[expose] def tcCoroots (E : TcEnv) (C : List ℕ) : List (Array ℤ) :=
  C.map fun i => (E.Cor.getD i #[]).map (· % (E.p : ℤ))

@[expose] def tcSplitCore (τ : Tag) (p : ℕ) (L : List (Array ℤ)) : Bool :=
  let E := tcEnv τ p L (tcSimpleGens τ.rank)
  let alc := tcAlcove τ p
  let OT : Thunk (Option TcOrb) := Thunk.mk fun _ => tcOrbVerified E
  tcLOK E &&
    alc.all fun μ =>
      tcIsZero p τ.rank μ || !tcInV E μ ||
        (let phi := (List.range E.R.size).filter fun r =>
            tcDot E.n (E.R.getD r #[]) μ % (p : ℤ) == 0
         let cls := tcClasses E.G phi
         tcClassesOK E.G phi cls &&
           cls.all fun C => tcCaseOK E OT alc true μ C (tcCoroots E C))

@[expose] def splitOK (τ : Tag) (p : ℕ) : Bool := tcSplitCore τ p []

@[expose] def tcT0Functional (_ : Unit := ()) : Array ℤ := #[1, 0, 2, 0, 1, 2]

@[expose] def tcCartanRows (τ : Tag) (_ : Unit := ()) : List (Array ℤ) := (tcCartan τ ()).toList

@[expose] def tcT0Check (_ : Unit := ()) : Bool :=
  let rows := tcCartanRows Tag.E6 ()
  let lam := tcT0Functional ()
  let ech := tcEchelon 3 6 rows
  rows.all (fun g => tcDot 6 lam g % 3 == 0) && tcEchOK 3 6 rows ech && ech.length == 5

@[expose] def splitT0OK (_ : Unit := ()) : Bool :=
  tcT0Check () && tcSplitCore .E6 3 [tcT0Functional ()]

@[expose] def tcGammaArr : Array ℕ := #[5, 1, 4, 3, 2, 0]

@[expose] def tcPermA (n : ℕ) (g : Array ℕ) (a : Array ℤ) : Array ℤ :=
  Array.ofFn (n := n) fun j => tcEnt a (g.getD j.val 0)

@[expose] def tcAddA (n : ℕ) (a b : Array ℤ) : Array ℤ :=
  Array.ofFn (n := n) fun j => tcEnt a j + tcEnt b j

@[expose] def tcGammaIdx (_ : Unit := ()) : Array ℕ :=
  let R := tcRoots Tag.E6 ()
  R.map fun a => (R.findIdx? (· == tcPermA 6 tcGammaArr a)).getD 0

@[expose] def tcTwistL (_ : Unit := ()) : List (Array ℤ) :=
  [#[-1, 0, 0, 0, 0, 1], #[0, 0, -1, 0, 1, 0]]

@[expose] def tcTwistGens (_ : Unit := ()) : Array (List ℕ) := #[[1], [3], [2, 4], [0, 5]]

@[expose] def tcGammaOK (E : TcEnv) (gI : Array ℕ) : Bool :=
  (List.range E.R.size).all fun i =>
    E.R.getD (gI.getD i 0) #[] == tcPermA E.n tcGammaArr (E.R.getD i #[]) &&
      (let x := tcAddA E.n (E.Cor.getD i #[]) (E.Cor.getD (gI.getD i 0) #[])
       tcPermA E.n tcGammaArr x == x)

@[expose] def tcTwistCore (p : ℕ) : Bool :=
  let E := tcEnv Tag.E6 p (tcTwistL ()) (tcTwistGens ())
  let gI := tcGammaIdx ()
  let OT : Thunk (Option TcOrb) := Thunk.mk fun _ => tcOrbVerified E
  tcLOK E && tcGammaOK E gI &&
    (List.range (p ^ Tag.E6.rank)).all fun m =>
      let b := tcDec p Tag.E6.rank m
      tcIsZero p Tag.E6.rank b || !tcInV E b ||
        (let phi := (List.range E.R.size).filter fun r =>
            tcDot E.n (E.R.getD r #[]) b % (p : ℤ) == 0
         let cls := tcClasses E.G phi
         tcClassesOK E.G phi cls &&
           cls.all fun C1 =>
             match cls.find? (·.contains (gI.getD (C1.headD 0) 0)) with
             | none => false
             | some C2 =>
               C1.all (fun x => C2.contains (gI.getD x 0)) &&
                 tcCaseOK E OT [] false b (C1 ++ C2)
                   (C1.map fun i =>
                     (tcAddA E.n (E.Cor.getD i #[]) (E.Cor.getD (gI.getD i 0) #[])).map
                       (· % (p : ℤ))))

@[expose] def twistOK (p : ℕ) : Bool := tcTwistCore p

end CFSG.StandardType.StepTwoToralCert


