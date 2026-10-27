module

public import CFSG.LieType.Ree.Mirror
public import CFSG.Blueprint.ChevalleyStringsInputs
public import CFSG.Monster.B.TwoA.Census.NatCert

public section

namespace Certificates.G2ThreeMax

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.Monster.B.TwoA.Census

@[expose] def idxOf (n : ℕ) : Idx g2Certificate :=
  if h : n < 2 then .inl ⟨n, h⟩
  else if h' : n - 2 < g2Certificate.roots.length then .inr ⟨n - 2, h'⟩
  else .inl ⟨0, by decide⟩

@[expose] def coefZ (u : Col g2Certificate) (r : Idx g2Certificate) : ℤ :=
  match u with
  | none => 0
  | some (a, n) => if a = r then n else 0

@[expose] def xEntry (c : ℤ) (i : Fin 2) (r b : Idx g2Certificate) : ℤ :=
  ∑ k ∈ Finset.range 4, c ^ k * coefZ (xCol g2Certificate g2StringData i k b) r

@[expose] def yEntry (c : ℤ) (i : Fin 2) (r b : Idx g2Certificate) : ℤ :=
  ∑ k ∈ Finset.range 4, c ^ k * coefZ (yCol g2Certificate g2StringData i k b) r

@[expose] def xArr (i : Fin 2) (c : ℤ) : Array ℕ :=
  Array.ofFn (n := 196) fun p => ((xEntry c i (idxOf (p.val / 14)) (idxOf (p.val % 14))) % 3).toNat

@[expose] def yArr (i : Fin 2) (c : ℤ) : Array ℕ :=
  Array.ofFn (n := 196) fun p => ((yEntry c i (idxOf (p.val / 14)) (idxOf (p.val % 14))) % 3).toNat

@[expose] def idArr : Array ℕ :=
  Array.ofFn (n := 196) fun p => if p.val / 14 = p.val % 14 then 1 else 0

@[expose] def genArr : ℕ → Array ℕ
  | 0 => xArr 0 1
  | 1 => xArr 0 (-1)
  | 2 => xArr 1 1
  | 3 => xArr 1 (-1)
  | 4 => yArr 0 1
  | 5 => yArr 0 (-1)
  | 6 => yArr 1 1
  | 7 => yArr 1 (-1)
  | _ => idArr

@[expose] def invK (k : ℕ) : ℕ := if k % 2 = 0 then k + 1 else k - 1

@[expose] def mmul (a b : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 196) fun p =>
    (∑ l ∈ Finset.range 14, a[14 * (p.val / 14) + l]! * b[14 * l + p.val % 14]!) % 3

@[expose] def wordArr (w : List ℕ) : Array ℕ := w.foldr (fun k acc => mmul (genArr k) acc) idArr

@[expose] def rowNZ (a : Array ℕ) (r : ℕ) : List (ℕ × ℕ) :=
  (List.range 14).filterMap fun l => if a[14 * r + l]! = 0 then none else some (l, a[14 * r + l]!)

@[expose] def colNZ (a : Array ℕ) (c : ℕ) : List (ℕ × ℕ) :=
  (List.range 14).filterMap fun l => if a[14 * l + c]! = 0 then none else some (l, a[14 * l + c]!)

@[expose] def rowsOf (a : Array ℕ) : Array (List (ℕ × ℕ)) := (Array.range 14).map (rowNZ a)

@[expose] def colsOf (a : Array ℕ) : Array (List (ℕ × ℕ)) := (Array.range 14).map (colNZ a)

@[expose] def conjSparse (rows cols : Array (List (ℕ × ℕ))) (P : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 196) fun p =>
    ((rows[p.val / 14]!).map fun t =>
      ((cols[p.val % 14]!).map fun u => t.2 * P[14 * t.1 + u.1]! * u.2).sum).sum % 3

@[expose] def encodeL : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 3 * encodeL ds

@[expose] def decodeAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => (n % 3) :: decodeAux k (n / 3)

@[expose] def encode (a : Array ℕ) : ℕ := encodeL a.toList

@[expose] def decode (n : ℕ) : Array ℕ := (decodeAux 196 n).toArray

@[expose] def rowsArr : Array (Array (List (ℕ × ℕ))) :=
  (Array.range 8).map fun k => rowsOf (genArr k)

@[expose] def colsInvArr (σ : List ℕ) : Array (Array (List (ℕ × ℕ))) :=
  (Array.range 8).map fun k => colsOf (genArr (invK σ[k]!))

@[expose] def actOf (cols : Array (Array (List (ℕ × ℕ)))) (k n : ℕ) : ℕ :=
  encode (conjSparse rowsArr[k]! cols[k]! (decode n))

@[expose] def tabOf (c : NatCert) (k i : ℕ) : ℕ := (c.edges[i]!)[k]!

@[expose] def applyW (c : NatCert) (w : List ℕ) (i : ℕ) : ℕ := w.foldr (fun k j => tabOf c k j) i

@[expose] def permArr (c : NatCert) (w : List ℕ) : Array ℕ := (Array.range c.pts.size).map (applyW c w)

@[expose] def pathWord (c : NatCert) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, i => if i = 0 then [] else c.lab[i]! :: pathWord c f c.par[i]!

@[expose] def hAct (hp : Array (Array ℕ)) (s i : ℕ) : ℕ := (hp[s]!)[i]!

@[expose] def repAct (hp : Array (Array ℕ)) (rp : Array ℕ) (s i : ℕ) : ℕ :=
  if s < hp.size then (hp[s]!)[i]! else rp[i]!

@[expose] def orbitSearch (act : ℕ → ℕ → ℕ) (nh N : ℕ) : List (ℕ × NatCert) :=
  ((List.range N).foldl (fun (st : Array Bool × List (ℕ × NatCert)) i =>
      if st.1[i]! then st else
        let c := natBfs act nh i N
        (c.pts.foldl (fun cov p => cov.set! p true) st.1, (i, c) :: st.2))
    (Array.replicate N false, [])).2.reverse

structure Input where
  sigma : List ℕ
  base : List ℕ
  stab : List (List ℕ)
  size : ℕ

@[expose] def stage1 (inp : Input) : NatCert :=
  natBfs (actOf (colsInvArr inp.sigma)) 8 (encode (wordArr inp.base)) inp.size

@[expose] def okSigma (inp : Input) : Bool := inp.sigma.length == 8 && inp.sigma.all (· < 8)

@[expose] def okInvol (inp : Input) : Bool := mmul (wordArr inp.base) (wordArr inp.base) == idArr

@[expose] def okStage1 (inp : Input) (c₁ : NatCert) : Bool :=
  natCertOK (actOf (colsInvArr inp.sigma)) 8 (fun _ => true) (encode (wordArr inp.base)) c₁ &&
    decide (c₁.pts.size = inp.size)

@[expose] def okNontriv (inp : Input) : Bool :=
  (List.range 8).any fun k =>
    conjSparse rowsArr[k]! (colsInvArr inp.sigma)[k]! (wordArr inp.base) != wordArr inp.base

@[expose] def okStab (inp : Input) (c₁ : NatCert) : Bool :=
  inp.stab.all fun w => w.all (· < 8) && applyW c₁ w 0 == 0

@[expose] def hpOf (inp : Input) (c₁ : NatCert) : Array (Array ℕ) :=
  (inp.stab.map (permArr c₁)).toArray

@[expose] def okOrbs (hp : Array (Array ℕ)) (N : ℕ) (orbs : List (ℕ × NatCert)) : Bool :=
  orbs.all (fun t => natCertOK (hAct hp) hp.size (fun u => decide (u < N)) t.1 t.2) &&
    (orbs.flatMap fun t => t.2.pts.toList).mergeSort (fun a b => decide (a ≤ b)) == List.range N

@[expose] def checkRep (c₁ : NatCert) (hp : Array (Array ℕ)) (N r : ℕ) : Bool :=
  let w := pathWord c₁ N r
  let rp := permArr c₁ w
  let c₃ := natBfs (repAct hp rp) (hp.size + 1) 0 N
  w.all (· < 8) && applyW c₁ w 0 == r &&
    natCertOK (repAct hp rp) (hp.size + 1) (fun u => decide (u < N)) 0 c₃ &&
    c₃.pts.toList.mergeSort (fun a b => decide (a ≤ b)) == List.range N

@[expose] def okTrans (c₁ : NatCert) (hp : Array (Array ℕ)) (N : ℕ) (orbs : List (ℕ × NatCert)) : Bool :=
  orbs.all fun t => t.1 == 0 || checkRep c₁ hp N t.1

@[expose] def primCheck (inp : Input) : Bool :=
  let c₁ := stage1 inp
  let hp := hpOf inp c₁
  let orbs := orbitSearch (hAct hp) hp.size c₁.pts.size
  okSigma inp && okInvol inp && okStage1 inp c₁ && okNontriv inp && okStab inp c₁ &&
    okOrbs hp c₁.pts.size orbs && okTrans c₁ hp c₁.pts.size orbs

@[expose] def innerInput : Input where
  sigma := [0, 1, 2, 3, 4, 5, 6, 7]
  base := [0, 5, 0, 0, 5, 0]
  stab := [[0], [1], [4], [5],
    [3, 1, 3, 1, 2, 6, 4, 6, 5, 6, 0, 6, 4, 7, 5, 7, 3, 0, 3, 0, 2],
    [7, 5, 0, 7, 3, 1, 7, 4, 7, 4, 1, 2],
    [3, 1, 3, 1, 7, 5, 6, 3, 5, 2, 4, 7, 4, 6, 0, 2, 0, 2],
    [3, 1, 2, 4, 0, 3, 6, 5, 7, 4, 2, 1, 4, 3, 6, 5, 6, 1, 2],
    [3, 0, 3, 5, 6, 5, 6, 5, 3, 6, 0, 5, 6, 5, 6, 2],
    [7, 2, 5, 1, 7, 2, 1, 4, 0, 4, 1, 2, 7, 5, 1, 3, 6]]
  size := 7371

@[expose] def outerInput : Input where
  sigma := [2, 3, 0, 1, 6, 7, 4, 5]
  base := []
  stab := [[2, 0, 5, 0, 6, 1, 7, 4, 1, 3], [2, 1, 6, 2, 1, 1, 3, 7, 1, 2, 1],
    [1, 6, 3, 5, 1, 7, 0, 5, 3, 6, 4, 0], [2, 0, 5, 6, 3, 5, 6, 0, 4, 6, 1, 3, 0],
    [1, 2, 5, 6, 1, 7, 0, 4, 3, 0], [1, 2, 6, 5, 0, 6, 0, 7, 0, 4, 7, 3, 0]]
  size := 2808

end Certificates.G2ThreeMax
