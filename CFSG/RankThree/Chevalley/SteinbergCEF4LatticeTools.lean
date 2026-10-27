module

public import CFSG.RankThree.Chevalley.SteinbergCEF4CharStabilizer

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace

namespace F4Weyl

@[expose] def f4Index (i : Fin 4) : Fin Tag.F4.rank := i

@[expose] def f4WordProd (l : List (Fin 4)) : WeylGroup .F4 :=
  (l.map fun i => simple .F4 (f4Index i)).prod

@[expose] def f4WordAct (l : List (Fin 4)) (v : Fin Tag.F4.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  l.foldr (fun i v => reflect .F4 (f4Index i) v) v

theorem f4WordProd_smul (l : List (Fin 4)) (v : Fin Tag.F4.rank → ℤ) :
    f4WordProd l • v = f4WordAct l v := by
  induction l with
  | nil => simp [f4WordProd, f4WordAct]
  | cons i l ih =>
    rw [f4WordProd, List.map_cons, List.prod_cons, mul_smul, ← f4WordProd, ih, simple_smul]
    rfl

theorem f4WordProd_append (l l' : List (Fin 4)) :
    f4WordProd (l ++ l') = f4WordProd l * f4WordProd l' := by
  rw [f4WordProd, List.map_append, List.prod_append, ← f4WordProd, ← f4WordProd]

theorem f4WordProd_pow (l : List (Fin 4)) (n : ℕ) :
    f4WordProd l ^ n = f4WordProd (List.replicate n l).flatten := by
  induction n with
  | zero => simp [f4WordProd]
  | succ n ih => rw [pow_succ, ih, ← f4WordProd_append, List.replicate_succ', List.flatten_append,
      List.flatten_singleton]

theorem weylMatrix_f4WordProd (l : List (Fin 4)) :
    weylMatrix (f4WordProd l) = Matrix.of fun i j => f4WordAct l (Pi.single j 1) i := by
  ext i j
  rw [weylMatrix_apply, f4WordProd_smul, Matrix.of_apply]

@[expose] def f4Coxeter : WeylGroup .F4 := f4WordProd [0, 1, 2, 3]

theorem f4Coxeter_pow (n : ℕ) :
    f4Coxeter ^ n = f4WordProd (List.replicate n [0, 1, 2, 3]).flatten :=
  f4WordProd_pow _ n

@[expose] def f4CoxeterMatrix : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![0, 1, 0, -1; 1, 1, 0, -1; 0, 2, 0, -1; 0, 0, 1, -1]

theorem weylMatrix_f4Coxeter : weylMatrix f4Coxeter = f4CoxeterMatrix := by
  rw [f4Coxeter, weylMatrix_f4WordProd]
  decide

theorem weylMatrix_simple_F4 (i : Fin Tag.F4.rank) :
    weylMatrix (simple .F4 i) = (reflT i).transpose := by
  ext k l
  rw [weylMatrix_apply, simple_smul, Matrix.transpose_apply, reflect]
  simp only [reflT, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hkl : k = l
  · subst hkl
    by_cases hki : k = i <;> simp [hki]
  · have hlk : l ≠ k := Ne.symm hkl
    by_cases hki : k = i
    · subst hki
      simp [hkl, hlk]
    · simp [hkl, hlk, hki]

theorem inv_f4WordProd_pair (i j : Fin 4) : (f4WordProd [i, j])⁻¹ = f4WordProd [j, i] := by
  simp only [f4WordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_inv_rev, (coxeterSystem .F4).inv_simple]

section Eigen

variable {R : Type*} [CommRing R]

theorem charVal_smul_of_dualMatrix_mulVec {v : Fin Tag.F4.rank → R} {w : WeylGroup .F4} {a : R}
    (h : (dualMatrix R w).mulVec v = a • v) (x : Fin Tag.F4.rank → ℤ) :
    charVal v (w • x) = a * charVal v x := by
  rw [← charVal_dualMatrix, h, charVal_smul_col]

theorem smul_mem_charRootKernel_iff
    {v : Fin Tag.F4.rank → R} {w : WeylGroup .F4} {a : Rˣ}
    (h : (dualMatrix R w).mulVec v = (a : R) • v) (α : Fin Tag.F4.rank → ℤ) :
    w • α ∈ charRootKernel v ↔ α ∈ charRootKernel v := by
  simp only [charRootKernel, Set.mem_ofPred_eq, isRoot_smul_iff,
    charVal_smul_of_dualMatrix_mulVec h, Units.mul_right_eq_zero]

end Eigen

theorem conj_smul_mem_parabolicRoots {S : Set (Fin Tag.F4.rank → ℤ)} {w u : WeylGroup .F4}
    {J : Set (Fin Tag.F4.rank)} (hS : ∀ α ∈ S, w • α ∈ S)
    (hu : (fun α => u • α) '' S = parabolicRoots .F4 J) :
    ∀ β ∈ parabolicRoots .F4 J, (u * w * u⁻¹) • β ∈ parabolicRoots .F4 J := by
  intro β hβ
  rw [← hu] at hβ ⊢
  obtain ⟨α, hα, rfl⟩ := hβ
  refine ⟨w • α, hS α hα, ?_⟩
  simp only [mul_smul, inv_smul_smul]

theorem parabolicRoots_empty : parabolicRoots .F4 (∅ : Set (Fin Tag.F4.rank)) = ∅ := by
  ext α
  simp only [parabolicRoots, Set.mem_ofPred_eq, Set.mem_empty_iff_false, not_false_eq_true,
    true_implies, iff_false, not_and]
  intro hα h0
  exact hα.ne_zero (funext h0)

@[expose] def f4RootList : List (Fin Tag.F4.rank → ℤ) :=
  (List.range Tag.F4.rootCertificate.roots.length).map Tag.F4.rootCertificate.root

theorem isRoot_iff_mem_f4RootList {v : Fin Tag.F4.rank → ℤ} : IsRoot .F4 v ↔ v ∈ f4RootList := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4), f4RootList, List.mem_map]
  simp only [List.mem_range]

@[expose] def parabolicRootList (J : Finset (Fin Tag.F4.rank)) : List (Fin Tag.F4.rank → ℤ) :=
  f4RootList.filter fun α => decide (∀ i, i ∉ J → α i = 0)

theorem mem_parabolicRootList {J : Finset (Fin Tag.F4.rank)} {α : Fin Tag.F4.rank → ℤ} :
    α ∈ parabolicRootList J ↔ α ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)) := by
  rw [parabolicRootList, List.mem_filter, ← isRoot_iff_mem_f4RootList, decide_eq_true_iff]
  rfl

@[expose] def colMap (c : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) (x : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → ℤ :=
  ∑ i, x i • c i

@[expose] def restrCols (J : Finset (Fin Tag.F4.rank)) (w : WeylGroup .F4) :
    Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  fun i => if i ∈ J then w • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) else 0

@[expose] def colCandidates (J : Finset (Fin Tag.F4.rank)) :
    List (Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) :=
  let L : Fin 4 → List (Fin Tag.F4.rank → ℤ) := fun i =>
    if f4Index i ∈ J then parabolicRootList J else [0]
  (L 0).flatMap fun c0 => (L 1).flatMap fun c1 => (L 2).flatMap fun c2 =>
    (L 3).map fun c3 => ![c0, c1, c2, c3]

theorem mem_colCandidates {J : Finset (Fin Tag.F4.rank)}
    {c : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ}
    (hc : ∀ i, c i ∈ (if i ∈ J then parabolicRootList J else [0])) : c ∈ colCandidates J := by
  have hc' : ∀ i : Fin 4, c (f4Index i) ∈
      (if f4Index i ∈ J then parabolicRootList J else [0]) := fun i => hc _
  have e : c = ![c (f4Index 0), c (f4Index 1), c (f4Index 2), c (f4Index 3)] := by
    funext i
    fin_cases i <;> rfl
  rw [e]
  exact List.mem_flatMap.2 ⟨_, hc' 0, List.mem_flatMap.2 ⟨_, hc' 1, List.mem_flatMap.2
    ⟨_, hc' 2, List.mem_map.2 ⟨_, hc' 3, rfl⟩⟩⟩⟩

theorem restrCols_mem_colCandidates
    {J : Finset (Fin Tag.F4.rank)} {w : WeylGroup .F4}
    (hw : ∀ β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)),
      w • β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank))) :
    restrCols J w ∈ colCandidates J := by
  refine mem_colCandidates fun i => ?_
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi, restrCols, ite_eq_left hi, mem_parabolicRootList]
    refine hw _ ⟨isRoot_single .F4 i, fun k hk => ?_⟩
    rw [Pi.single_apply, ite_eq_right]
    rintro rfl
    exact hk hi
  · rw [ite_eq_right hi, restrCols, ite_eq_right hi]
    exact List.mem_singleton_self _

@[expose] def colChoices (J : Finset (Fin Tag.F4.rank)) (i : Fin Tag.F4.rank) :
    List (Fin Tag.F4.rank → ℤ) :=
  if i ∈ J then parabolicRootList J else [0]

theorem restrCols_mem_colChoices
    {J : Finset (Fin Tag.F4.rank)} {w : WeylGroup .F4}
    (hw : ∀ β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)),
      w • β ∈ parabolicRoots .F4 (J : Set (Fin Tag.F4.rank))) (i : Fin Tag.F4.rank) :
    restrCols J w i ∈ colChoices J i := by
  by_cases hi : i ∈ J
  · rw [colChoices, ite_eq_left hi, restrCols, ite_eq_left hi, mem_parabolicRootList]
    refine hw _ ⟨isRoot_single .F4 i, fun k hk => ?_⟩
    rw [Pi.single_apply, ite_eq_right]
    rintro rfl
    exact hk hi
  · rw [colChoices, ite_eq_right hi, restrCols, ite_eq_right hi]
    exact List.mem_singleton_self _

theorem eq_vecCons_cols (c : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) :
    c = ![c (f4Index 0), c (f4Index 1), c (f4Index 2), c (f4Index 3)] := by
  funext i
  fin_cases i <;> rfl

@[expose] def cols4 (c₀ c₁ c₂ c₃ : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  fun i => if i = f4Index 0 then c₀ else if i = f4Index 1 then c₁ else
    if i = f4Index 2 then c₂ else c₃

theorem eq_cols4 (c : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) :
    c = cols4 (c (f4Index 0)) (c (f4Index 1)) (c (f4Index 2)) (c (f4Index 3)) := by
  funext i
  have h : ∀ k : Fin Tag.F4.rank, k = f4Index 0 ∨ k = f4Index 1 ∨ k = f4Index 2 ∨
      k = f4Index 3 := by decide
  have h10 : f4Index 1 ≠ f4Index 0 := by decide
  have h20 : f4Index 2 ≠ f4Index 0 := by decide
  have h21 : f4Index 2 ≠ f4Index 1 := by decide
  have h30 : f4Index 3 ≠ f4Index 0 := by decide
  have h31 : f4Index 3 ≠ f4Index 1 := by decide
  have h32 : f4Index 3 ≠ f4Index 2 := by decide
  rcases h i with rfl | rfl | rfl | rfl
  · rw [cols4, ite_eq_left rfl]
  · rw [cols4, ite_eq_right h10, ite_eq_left rfl]
  · rw [cols4, ite_eq_right h20, ite_eq_right h21, ite_eq_left rfl]
  · rw [cols4, ite_eq_right h30, ite_eq_right h31, ite_eq_right h32]

theorem smul_eq_colMap_restrCols (J : Finset (Fin Tag.F4.rank)) (w : WeylGroup .F4)
    {x : Fin Tag.F4.rank → ℤ} (hx : ∀ i, i ∉ J → x i = 0) :
    w • x = colMap (restrCols J w) x := by
  rw [smul_eq_sum_smul_single w x, colMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ J
  · rw [restrCols, ite_eq_left hi]
  · rw [hx i hi, zero_smul, zero_smul]

theorem restrCols_f4WordProd (J : Finset (Fin Tag.F4.rank)) (l : List (Fin 4)) :
    restrCols J (f4WordProd l) =
      fun i => if i ∈ J then f4WordAct l (Pi.single i 1 : Fin Tag.F4.rank → ℤ) else 0 := by
  funext i
  rw [restrCols, f4WordProd_smul]

theorem conj_quadratic {w : WeylGroup .F4} {a b c : ℤ}
    (h : ∀ x : Fin Tag.F4.rank → ℤ, a • (w • (w • x)) + b • (w • x) + c • x = 0)
    (u : WeylGroup .F4) (x : Fin Tag.F4.rank → ℤ) :
    a • ((u * w * u⁻¹) • ((u * w * u⁻¹) • x)) + b • ((u * w * u⁻¹) • x) + c • x = 0 := by
  have h1 := congrArg (u • ·) (h (u⁻¹ • x))
  simp only [smul_add, smul_zero, smul_comm u a, smul_comm u b, smul_comm u c, smul_inv_smul]
    at h1
  simpa only [mul_smul, inv_smul_smul] using h1

theorem coe_pair_finset (i j : Fin Tag.F4.rank) :
    ((({i, j} : Finset (Fin Tag.F4.rank))) : Set (Fin Tag.F4.rank)) = {i, j} := by
  rw [Finset.coe_insert, Finset.coe_singleton]

theorem parabolicRoots_eq_toFinset (J : Finset (Fin Tag.F4.rank)) :
    parabolicRoots .F4 (J : Set (Fin Tag.F4.rank)) = ↑(parabolicRootList J).toFinset := by
  ext α
  rw [Finset.mem_coe, List.mem_toFinset, mem_parabolicRootList]

theorem f4WordProd_pair (i j : Fin 4) :
    f4WordProd [i, j] = simple .F4 (f4Index i) * simple .F4 (f4Index j) := by
  simp only [f4WordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem weylAct_eqOn_span {τ : Tag} {g g' : WeylGroup τ} {S : Set (Fin τ.rank → ℤ)}
    (h : ∀ β ∈ S, g • β = g' • β) :
    ∀ x ∈ Submodule.span ℝ (ofLattice '' S), weylAct τ g x = weylAct τ g' x := by
  intro x hx
  have heq : Set.EqOn ((weylAct τ g).toLinearEquiv.toLinearMap)
      ((weylAct τ g').toLinearEquiv.toLinearMap) (ofLattice '' S) := by
    rintro _ ⟨β, hβ, rfl⟩
    change weylAct τ g (ofLattice β) = weylAct τ g' (ofLattice β)
    rw [weylAct_ofLattice, weylAct_ofLattice, h β hβ]
  exact LinearMap.eqOn_span' heq hx

end F4Weyl

end CFSG.RankThree.Chevalley
