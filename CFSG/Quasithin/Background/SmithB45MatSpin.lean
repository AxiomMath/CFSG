module

public import CFSG.CharacterTheory.SteinbergBYNortonCriterion

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.CharacterTheory.SteinbergBY Matrix
open scoped Kronecker

section Map

variable {F F' : Type*}

@[expose] def mapTab (f : F → F') {m n : ℕ} (A : Vector (Vector F n) m) :
    Vector (Vector F' n) m :=
  A.map fun r => r.map f

theorem untab_mapTab (f : F → F') {m n : ℕ} (A : Vector (Vector F n) m) :
    untab (mapTab f A) = (untab A).map f := by
  ext i j
  simp [mapTab, untab]

end Map

section Tables

variable {F : Type*} [Semiring F]

theorem foldl_add_eq_sum (n : ℕ) (f : Fin n → F) (c : F) :
    Fin.foldl n (fun acc l => acc + f l) c = c + ∑ l, f l := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc, ← add_assoc]
    exact congrArg (· + f (Fin.last n)) (ih (fun l => f l.castSucc) c)

@[expose] def mulT {k m n : ℕ} (A : Vector (Vector F m) k) (B : Vector (Vector F n) m) :
    Vector (Vector F n) k :=
  Vector.ofFn fun i => Vector.ofFn fun j => Fin.foldl m (fun acc l => acc + A[i][l] * B[l][j]) 0

theorem untab_mulT {k m n : ℕ} (A : Vector (Vector F m) k) (B : Vector (Vector F n) m) :
    untab (mulT A B) = untab A * untab B := by
  ext i j
  rw [untab_apply, Matrix.mul_apply]
  simp only [mulT, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [foldl_add_eq_sum, zero_add]
  rfl

@[expose] def mulVecT {k m : ℕ} (A : Vector (Vector F m) k) (x : Vector F m) : Vector F k :=
  Vector.ofFn fun i => Fin.foldl m (fun acc l => acc + A[i][l] * x[l]) 0

theorem mulVecT_spec {k m : ℕ} (A : Vector (Vector F m) k) (x : Vector F m) :
    (fun i : Fin k => (mulVecT A x)[i]) = untab A *ᵥ fun l => x[l] := by
  funext i
  simp only [mulVecT, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [foldl_add_eq_sum, zero_add]
  rfl

@[expose] def vecMulT {k m : ℕ} (x : Vector F k) (A : Vector (Vector F m) k) : Vector F m :=
  Vector.ofFn fun j => Fin.foldl k (fun acc l => acc + x[l] * A[l][j]) 0

theorem vecMulT_spec {k m : ℕ} (x : Vector F k) (A : Vector (Vector F m) k) :
    (fun j : Fin m => (vecMulT x A)[j]) = (fun l => x[l]) ᵥ* untab A := by
  funext j
  simp only [vecMulT, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [foldl_add_eq_sum, zero_add]
  rfl

@[expose] def kronTab {m n : ℕ} (A : Vector (Vector F m) m) (B : Vector (Vector F n) n) :
    Vector (Vector F (m * n)) (m * n) :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    A[(finProdFinEquiv.symm i).1][(finProdFinEquiv.symm j).1] *
      B[(finProdFinEquiv.symm i).2][(finProdFinEquiv.symm j).2]

theorem untab_kronTab {m n : ℕ} (A : Vector (Vector F m) m) (B : Vector (Vector F n) n) :
    untab (kronTab A B) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (untab A ⊗ₖ untab B) := by
  ext i j
  simp [kronTab, untab, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

@[expose] def idT (n : ℕ) : Vector (Vector F n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j then 1 else 0

theorem untab_idT (n : ℕ) : untab (idT n : Vector (Vector F n) n) = 1 := by
  ext i j
  simp [untab_apply, idT, Matrix.one_apply]

end Tables

section Words

variable {F : Type*} [Semiring F] {n : ℕ}

@[expose] def genT (Ma Mb : Vector (Vector F n) n) (z : Bool) : Vector (Vector F n) n :=
  if z then Mb else Ma

@[expose] def wordT (Ma Mb : Vector (Vector F n) n) : List Bool → Vector (Vector F n) n
  | [] => idT n
  | [z] => genT Ma Mb z
  | z :: y :: w => mulT (genT Ma Mb z) (wordT Ma Mb (y :: w))

@[expose] def wordG {G : Type*} [Group G] (a b : G) : List Bool → G
  | [] => 1
  | z :: w => (if z then b else a) * wordG a b w

variable {G : Type*} [Group G] (M : G →* Matrix (Fin n) (Fin n) F) {a b : G}
  {Ma Mb : Vector (Vector F n) n}

theorem untab_genT (ha : untab Ma = M a) (hb : untab Mb = M b) (z : Bool) :
    untab (genT Ma Mb z) = M (if z then b else a) := by
  cases z
  · exact ha
  · exact hb

theorem untab_wordT (ha : untab Ma = M a) (hb : untab Mb = M b) :
    ∀ w : List Bool, untab (wordT Ma Mb w) = M (wordG a b w)
  | [] => by rw [wordT, untab_idT, wordG, map_one]
  | [z] => by rw [wordT, wordG, wordG, mul_one, untab_genT M ha hb]
  | z :: y :: w => by
    rw [wordT, untab_mulT, untab_wordT ha hb (y :: w), untab_genT M ha hb]
    exact (map_mul M _ _).symm

end Words

section Spin

variable {F : Type*} [Semiring F] {n : ℕ}

@[expose] def spinStep (Ma Mb : Vector (Vector F n) n) (v : Vector F n)
    (acc : Array (Vector F n)) (e : ℕ × Bool) : Array (Vector F n) :=
  acc.push (mulVecT (genT Ma Mb e.2) (acc.getD e.1 v))

@[expose] def spinVecs (Ma Mb : Vector (Vector F n) n) (v : Vector F n)
    (prog : List (ℕ × Bool)) : Array (Vector F n) :=
  prog.foldl (spinStep Ma Mb v) #[v]

@[expose] def colTab (vs : Array (Vector F n)) (v : Vector F n) : Vector (Vector F n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => (vs.getD j v)[i]

@[expose] def dualStep (Ma Mb : Vector (Vector F n) n) (w : Vector F n)
    (acc : Array (Vector F n)) (e : ℕ × Bool) : Array (Vector F n) :=
  acc.push (vecMulT (acc.getD e.1 w) (genT Ma Mb e.2))

@[expose] def dualVecs (Ma Mb : Vector (Vector F n) n) (w : Vector F n)
    (prog : List (ℕ × Bool)) : Array (Vector F n) :=
  prog.foldl (dualStep Ma Mb w) #[w]

@[expose] def rowTab (ws : Array (Vector F n)) (w : Vector F n) : Vector (Vector F n) n :=
  Vector.ofFn fun i => ws.getD i w

theorem getD_push {α : Type*} (acc : Array α) (x d : α) (k : ℕ) :
    (acc.push x).getD k d = if k = acc.size then x else acc.getD k d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs <;> rfl

variable {G : Type*} [Group G] (M : G →* Matrix (Fin n) (Fin n) F) {a b : G}
  {Ma Mb : Vector (Vector F n) n}

theorem spinVecs_spec (ha : untab Ma = M a) (hb : untab Mb = M b) (v : Vector F n)
    (prog : List (ℕ × Bool)) (k : ℕ) :
    ∃ g, (fun i : Fin n => ((spinVecs Ma Mb v prog).getD k v)[i]) = M g *ᵥ fun i => v[i] := by
  have key : ∀ (prog : List (ℕ × Bool)) (acc : Array (Vector F n)),
      (∀ k, ∃ g, (fun i : Fin n => (acc.getD k v)[i]) = M g *ᵥ fun i => v[i]) →
      ∀ k, ∃ g, (fun i : Fin n => ((prog.foldl (spinStep Ma Mb v) acc).getD k v)[i]) =
        M g *ᵥ fun i => v[i] := by
    intro prog
    induction prog with
    | nil => exact fun acc h => h
    | cons e es ih =>
      intro acc h
      refine ih _ fun k => ?_
      rw [spinStep, getD_push]
      split_ifs
      · obtain ⟨g, hg⟩ := h e.1
        refine ⟨(if e.2 then b else a) * g, ?_⟩
        rw [mulVecT_spec, hg, untab_genT M ha hb, Matrix.mulVec_mulVec, map_mul]
      · exact h k
  refine key prog #[v] (fun k => ⟨1, ?_⟩) k
  rw [map_one, Matrix.one_mulVec]
  funext i
  simp only [Array.getD_eq_getD_getElem?]
  rcases k with _ | k
  · rfl
  · rfl

theorem dualVecs_spec (ha : untab Ma = M a) (hb : untab Mb = M b) (w : Vector F n)
    (prog : List (ℕ × Bool)) (k : ℕ) :
    ∃ g, (fun i : Fin n => ((dualVecs Ma Mb w prog).getD k w)[i]) = (fun i => w[i]) ᵥ* M g := by
  have key : ∀ (prog : List (ℕ × Bool)) (acc : Array (Vector F n)),
      (∀ k, ∃ g, (fun i : Fin n => (acc.getD k w)[i]) = (fun i => w[i]) ᵥ* M g) →
      ∀ k, ∃ g, (fun i : Fin n => ((prog.foldl (dualStep Ma Mb w) acc).getD k w)[i]) =
        (fun i => w[i]) ᵥ* M g := by
    intro prog
    induction prog with
    | nil => exact fun acc h => h
    | cons e es ih =>
      intro acc h
      refine ih _ fun k => ?_
      rw [dualStep, getD_push]
      split_ifs
      · obtain ⟨g, hg⟩ := h e.1
        refine ⟨g * (if e.2 then b else a), ?_⟩
        rw [vecMulT_spec, hg, untab_genT M ha hb, Matrix.vecMul_vecMul, map_mul]
      · exact h k
  refine key prog #[w] (fun k => ⟨1, ?_⟩) k
  rw [map_one, Matrix.vecMul_one]
  funext i
  simp only [Array.getD_eq_getD_getElem?]
  rcases k with _ | k
  · rfl
  · rfl

end Spin

section Norton

variable {F : Type*} [Field F] {n : ℕ}

structure SpinData (F : Type*) (n : ℕ) where
  terms : List (List Bool × F)
  Q : Vector (Vector F n) n
  Qi : Vector (Vector F n) n
  R : Vector (Vector F n) n
  spin : List (ℕ × Bool)
  Si : Vector (Vector F n) n
  w : Vector F n
  dual : List (ℕ × Bool)
  Ti : Vector (Vector F n) n

@[expose] def SpinData.check [DecidableEq F] [NeZero n] (d : SpinData F n)
    (Ma Mb : Vector (Vector F n) n) : Bool :=
  let A := sumTerms (d.terms.map fun t => (t.2, wordT Ma Mb t.1))
  let v : Vector F n := Vector.ofFn fun l => d.Q[l][(0 : Fin n)]
  decide (untab (mulT d.Qi d.Q) = 1) &&
  decide (untab (mulT (mulT d.R A) d.Q) =
    Matrix.diagonal fun j : Fin n => if j = 0 then 0 else 1) &&
  decide (untab (mulT d.Si (colTab (spinVecs Ma Mb v d.spin) v)) = 1) &&
  decide (∀ j : Fin n, (vecMulT d.w A)[j] = 0) &&
  decide (untab (mulT d.Ti (rowTab (dualVecs Ma Mb d.w d.dual) d.w)) = 1)

theorem SpinData.isIrreducible_of_check {G K : Type*} [Group G] [Field K] [DecidableEq F]
    [NeZero n] (φ : F →+* K) (M : G →* Matrix (Fin n) (Fin n) F) {a b : G}
    {Ma Mb : Vector (Vector F n) n} (ha : untab Ma = M a) (hb : untab Mb = M b)
    (d : SpinData F n) (h : d.check Ma Mb = true) : (matrixBaseChange φ M).IsIrreducible := by
  simp only [SpinData.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hQ, hR⟩, hS⟩, hw⟩, hT⟩ := h
  set v : Vector F n := Vector.ofFn fun l => d.Q[l][(0 : Fin n)] with hv
  set l : List (G × F) := d.terms.map fun t => (wordG a b t.1, t.2) with hl
  have hA : untab (sumTerms (d.terms.map fun t => (t.2, wordT Ma Mb t.1))) =
      (l.map fun p => p.2 • M p.1).sum := by
    rw [sumTerms, untab_tab, List.map_map, hl, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, untab_wordT M ha hb]
  rw [untab_mulT, untab_mulT, hA] at hR
  rw [untab_mulT] at hQ hS hT
  refine isIrreducible_matrixBaseChange_of_cert φ M l (untab d.Q) (untab d.Qi) (untab d.R) hQ hR
    (untab (colTab (spinVecs Ma Mb v d.spin) v)) (untab d.Si) (fun j => ?_) hS
    (fun l => d.w[l]) ?_ (untab (rowTab (dualVecs Ma Mb d.w d.dual) d.w)) (untab d.Ti)
    (fun i => ?_) hT
  · obtain ⟨g, hg⟩ := spinVecs_spec M ha hb v d.spin j
    refine ⟨g, fun i => ?_⟩
    have h1 := congrFun hg i
    simp only [colTab, untab_apply, Fin.getElem_fin, Vector.getElem_ofFn] at h1 ⊢
    rw [h1, hv]
    congr 2
    funext l
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  · rw [← hA, ← vecMulT_spec]
    funext j
    exact hw j
  · obtain ⟨g, hg⟩ := dualVecs_spec M ha hb d.w d.dual i
    refine ⟨g, fun j => ?_⟩
    have h1 := congrFun hg j
    simp only [rowTab, untab_apply, Fin.getElem_fin, Vector.getElem_ofFn] at h1 ⊢
    exact h1

end Norton

section Invariant

variable {F : Type*} [Field F] [DecidableEq F] {n d : ℕ}

@[expose] def subOK (Ka Kb : Vector (Vector F n) n) (B : Vector (Vector F d) n)
    (P : Vector (Vector F n) d) : Bool :=
  decide (untab (mulT P B) = 1) && [Ka, Kb].all fun K =>
    let KB := mulT K B
    decide (untab KB = untab (mulT B (mulT P KB)))

@[expose] def quotOK (Ka Kb : Vector (Vector F n) n) (B : Vector (Vector F d) n)
    (P : Vector (Vector F n) d) : Bool :=
  decide (untab (mulT P B) = 1) && [Ka, Kb].all fun K =>
    let PK := mulT P K
    decide (untab PK = untab (mulT (mulT PK B) P))

theorem subOK_spec {Ka Kb : Vector (Vector F n) n} {B : Vector (Vector F d) n}
    {P : Vector (Vector F n) d} (h : subOK Ka Kb B P = true) :
    untab P * untab B = 1 ∧ ∀ K ∈ [Ka, Kb],
      untab K * untab B = untab B * (untab P * untab K * untab B) := by
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, untab_mulT] at h
  refine ⟨h.1, fun K hK => ?_⟩
  rw [Matrix.mul_assoc (untab P)]
  exact h.2 K hK

theorem quotOK_spec {Ka Kb : Vector (Vector F n) n} {B : Vector (Vector F d) n}
    {P : Vector (Vector F n) d} (h : quotOK Ka Kb B P = true) :
    untab P * untab B = 1 ∧ ∀ K ∈ [Ka, Kb],
      untab P * untab K = untab P * untab K * untab B * untab P := by
  simp only [quotOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, untab_mulT] at h
  exact ⟨h.1, h.2⟩

end Invariant

end CFSG.Quasithin.B45Mat
