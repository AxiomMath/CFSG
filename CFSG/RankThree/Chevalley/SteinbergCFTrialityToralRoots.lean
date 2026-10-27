module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

namespace TrialityFold

abbrev i0 : Fin TwistTag.D4.tag.rank := ⟨0, by decide⟩
abbrev i1 : Fin TwistTag.D4.tag.rank := ⟨1, by decide⟩
abbrev i2 : Fin TwistTag.D4.tag.rank := ⟨2, by decide⟩
abbrev i3 : Fin TwistTag.D4.tag.rank := ⟨3, by decide⟩

theorem fin_cases (j : Fin TwistTag.D4.tag.rank) : j = i0 ∨ j = i1 ∨ j = i2 ∨ j = i3 := by
  revert j
  decide

@[expose] def fold (v : Fin TwistTag.D4.tag.rank → ℤ) : ℤ × ℤ :=
  (v i0 + v i1 + v i3, v i2)

theorem fold_add (u v : Fin TwistTag.D4.tag.rank → ℤ) : fold (u + v) = fold u + fold v := by
  simp only [fold, Pi.add_apply, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  ring

theorem fold_neg (v : Fin TwistTag.D4.tag.rank → ℤ) : fold (-v) = -fold v := by
  simp only [fold, Pi.neg_apply, Prod.neg_mk, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  ring

theorem fold_zsmul (n : ℤ) (v : Fin TwistTag.D4.tag.rank → ℤ) : fold (n • v) = n • fold v := by
  simp only [fold, Pi.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  ring

theorem fold_single0 : fold (Pi.single i0 1) = (1, 0) := by decide
theorem fold_single1 : fold (Pi.single i1 1) = (1, 0) := by decide
theorem fold_single2 : fold (Pi.single i2 1) = (0, 1) := by decide
theorem fold_single3 : fold (Pi.single i3 1) = (1, 0) := by decide

theorem perm_symm_i0 : TwistTag.D4.perm.symm i0 = i3 := by decide
theorem perm_symm_i1 : TwistTag.D4.perm.symm i1 = i0 := by decide
theorem perm_symm_i2 : TwistTag.D4.perm.symm i2 = i2 := by decide
theorem perm_symm_i3 : TwistTag.D4.perm.symm i3 = i1 := by decide

theorem fold_permLattice (v : Fin TwistTag.D4.tag.rank → ℤ) :
    fold (permLattice TwistTag.D4.perm v) = fold v := by
  simp only [fold, permLattice, Function.comp_apply, perm_symm_i0, perm_symm_i1, perm_symm_i2,
    perm_symm_i3, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  ring

@[expose] def foldChar {G : Type*} [Group G] (A B : G) (μ : ℤ × ℤ) : G := A ^ μ.1 * B ^ μ.2

theorem foldChar_add {G : Type*} [CommGroup G] (A B : G) (μ ν : ℤ × ℤ) :
    foldChar A B (μ + ν) = foldChar A B μ * foldChar A B ν := by
  simp only [foldChar, Prod.fst_add, Prod.snd_add, zpow_add]
  rw [mul_mul_mul_comm]

theorem foldChar_neg {G : Type*} [CommGroup G] (A B : G) (μ : ℤ × ℤ) :
    foldChar A B (-μ) = (foldChar A B μ)⁻¹ := by
  simp only [foldChar, Prod.fst_neg, Prod.snd_neg, zpow_neg, mul_inv]

theorem rootChar_eq_foldChar {K : Type} [Field K] {a : Fin TwistTag.D4.tag.rank → Kˣ}
    {A B : Kˣ} (h0 : a i0 = A) (h1 : a i1 = A) (h2 : a i2 = B) (h3 : a i3 = A)
    (v : Fin TwistTag.D4.tag.rank → ℤ) : rootChar a v = foldChar A B (fold v) := by
  have huniv : (Finset.univ : Finset (Fin TwistTag.D4.tag.rank)) = {i0, i1, i2, i3} := by decide
  rw [rootChar, huniv, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, h0, h1, h2, h3, foldChar, fold,
    zpow_add, zpow_add]
  rw [mul_comm (B ^ v i2) (A ^ v i3)]
  simp only [mul_assoc]

theorem foldChar_det {G : Type*} [CommGroup G] {A B : G} {x y : ℤ × ℤ}
    (hx : foldChar A B x = 1) (hy : foldChar A B y = 1) :
    A ^ (x.1 * y.2 - x.2 * y.1) = 1 ∧ B ^ (x.1 * y.2 - x.2 * y.1) = 1 := by
  rw [foldChar] at hx hy
  constructor
  · have e : A ^ (x.1 * y.2 - x.2 * y.1) =
        (A ^ x.1 * B ^ x.2) ^ y.2 * (A ^ y.1 * B ^ y.2) ^ (-x.2) := by
      rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm,
        ← zpow_add, ← zpow_add, show x.2 * y.2 + y.2 * -x.2 = 0 by ring, zpow_zero, mul_one]
      congr 1
      ring
    rw [e, hx, hy, one_zpow, one_zpow, mul_one]
  · have e : B ^ (x.1 * y.2 - x.2 * y.1) =
        (A ^ x.1 * B ^ x.2) ^ (-y.1) * (A ^ y.1 * B ^ y.2) ^ x.1 := by
      rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm,
        ← zpow_add, ← zpow_add, show x.1 * -y.1 + y.1 * x.1 = 0 by ring, zpow_zero, one_mul]
      congr 1
      ring
    rw [e, hx, hy, one_zpow, one_zpow, mul_one]

@[expose] def g2FoldRoots : List (ℤ × ℤ) :=
  [(1, 0), (0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (-1, 0), (0, -1), (-1, -1), (-2, -1),
    (-3, -1), (-3, -2)]

@[expose] def foldL (l : List ℤ) : ℤ × ℤ := (l.getD 0 0 + l.getD 1 0 + l.getD 3 0, l.getD 2 0)

@[expose] def rhoL (l : List ℤ) : List ℤ := [l.getD 3 0, l.getD 0 0, l.getD 2 0, l.getD 1 0]

theorem foldL_ofFn (v : Fin TwistTag.D4.tag.rank → ℤ) : foldL (List.ofFn v) = fold v := rfl

theorem rhoL_ofFn (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rhoL (List.ofFn v) = List.ofFn (permLattice TwistTag.D4.perm v) := by
  change [v i3, v i0, v i2, v i1] = [v (TwistTag.D4.perm.symm i0), v (TwistTag.D4.perm.symm i1),
    v (TwistTag.D4.perm.symm i2), v (TwistTag.D4.perm.symm i3)]
  rw [perm_symm_i0, perm_symm_i1, perm_symm_i2, perm_symm_i3]

theorem foldL_mem_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots, foldL l ∈ g2FoldRoots := by decide

theorem fiber_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots, ∀ m ∈ TwistTag.D4.tag.artifactRoots,
    foldL m = foldL l → m = l ∨ m = rhoL l ∨ m = rhoL (rhoL l) := by decide

theorem det_check : ∀ r ∈ g2FoldRoots, ∀ s ∈ g2FoldRoots,
    s = r ∨ s = -r ∨ r.1 * s.2 - r.2 * s.1 ∈ ([1, 2, 3, -1, -2, -3] : List ℤ) := by decide

theorem ofFn_getD_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots,
    List.ofFn (fun i : Fin TwistTag.D4.tag.rank => l.getD i 0) = l := by decide

theorem fold_surj_check : ∀ μ ∈ g2FoldRoots, ∃ l ∈ TwistTag.D4.tag.artifactRoots, foldL l = μ := by
  decide

theorem fold_mem_of_isRoot {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α) :
    fold α ∈ g2FoldRoots := by
  rw [← foldL_ofFn]
  exact foldL_mem_check _ (isRoot_iff_mem_artifactRoots.1 hα)

theorem exists_isRoot_fold_eq {μ : ℤ × ℤ} (hμ : μ ∈ g2FoldRoots) :
    ∃ β, IsRoot TwistTag.D4.tag β ∧ fold β = μ := by
  obtain ⟨l, hl, hlμ⟩ := fold_surj_check μ hμ
  refine ⟨fun i => l.getD i 0, isRoot_iff_mem_artifactRoots.2 ?_, ?_⟩
  · rw [ofFn_getD_check l hl]
    exact hl
  · rw [← foldL_ofFn, ofFn_getD_check l hl, hlμ]

theorem permLattice_mul_apply (g h : Equiv.Perm (Fin TwistTag.D4.tag.rank))
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice (g * h) v = permLattice g (permLattice h v) := rfl

theorem fold_permLattice_pow (k : ℕ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    fold (permLattice (TwistTag.D4.perm ^ k) v) = fold v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', permLattice_mul_apply, fold_permLattice, ih]

theorem fold_eq_of_mem_diagramOrbit {α β : Fin TwistTag.D4.tag.rank → ℤ}
    (h : β ∈ TwistTag.D4.diagramOrbit α) : fold β = fold α := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
  exact fold_permLattice_pow k α

theorem mem_diagramOrbit_of_fold_eq {α β : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hβ : IsRoot TwistTag.D4.tag β) (h : fold β = fold α) :
    β ∈ TwistTag.D4.diagramOrbit α := by
  have hfib := fiber_check _ (isRoot_iff_mem_artifactRoots.1 hα) _
    (isRoot_iff_mem_artifactRoots.1 hβ) (by rw [foldL_ofFn, foldL_ofFn, h])
  rw [rhoL_ofFn, rhoL_ofFn] at hfib
  refine Finset.mem_image.2 ?_
  rcases hfib with h0 | h1 | h2
  · exact ⟨0, by decide, (List.ofFn_injective h0).symm⟩
  · exact ⟨1, by decide, by rw [pow_one]; exact (List.ofFn_injective h1).symm⟩
  · exact ⟨2, by decide, by
      rw [pow_two, permLattice_mul_apply]
      exact (List.ofFn_injective h2).symm⟩

theorem mem_diagramOrbit_iff_fold_eq {α β : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hβ : IsRoot TwistTag.D4.tag β) :
    β ∈ TwistTag.D4.diagramOrbit α ↔ fold β = fold α :=
  ⟨fold_eq_of_mem_diagramOrbit, mem_diagramOrbit_of_fold_eq hα hβ⟩

theorem smul_permLattice_of_mem {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    w • permLattice TwistTag.D4.perm v = permLattice TwistTag.D4.perm (w • v) := by
  have h := weylTwist_smul_permLattice TwistTag.D4 w v
  rwa [(mem_relWeylTwist TwistTag.D4).1 hw] at h

@[expose] def foldPair (w : WeylGroup TwistTag.D4.tag) : (ℤ × ℤ) × (ℤ × ℤ) :=
  (fold (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ)),
    fold (w • (Pi.single i2 1 : Fin TwistTag.D4.tag.rank → ℤ)))

@[expose] def applyP (P : (ℤ × ℤ) × (ℤ × ℤ)) (μ : ℤ × ℤ) : ℤ × ℤ := μ.1 • P.1 + μ.2 • P.2

theorem applyP_neg (P : (ℤ × ℤ) × (ℤ × ℤ)) (μ : ℤ × ℤ) : applyP P (-μ) = -applyP P μ := by
  simp only [applyP, Prod.fst_neg, Prod.snd_neg, neg_smul, neg_add]

theorem perm_i0 : TwistTag.D4.perm i0 = i1 := by decide
theorem perm_i1 : TwistTag.D4.perm i1 = i3 := by decide

theorem single_i1_eq : (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ) =
    permLattice TwistTag.D4.perm (Pi.single i0 1) := by
  rw [permLattice_single, perm_i0]

theorem single_i3_eq : (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ) =
    permLattice TwistTag.D4.perm (permLattice TwistTag.D4.perm (Pi.single i0 1)) := by
  rw [← single_i1_eq, permLattice_single, perm_i1]

theorem fold_smul {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (v : Fin TwistTag.D4.tag.rank → ℤ) : fold (w • v) = applyP (foldPair w) (fold v) := by
  have hv : v = v i0 • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) +
      v i1 • Pi.single i1 1 + v i2 • Pi.single i2 1 + v i3 • Pi.single i3 1 := by
    funext j
    rcases fin_cases j with rfl | rfl | rfl | rfl <;> simp
  conv_lhs => rw [hv]
  rw [smul_add, smul_add, smul_add, smul_comm w (v i0), smul_comm w (v i1), smul_comm w (v i2),
    smul_comm w (v i3), fold_add, fold_add, fold_add, fold_zsmul, fold_zsmul, fold_zsmul,
    fold_zsmul, single_i3_eq, single_i1_eq]
  simp only [smul_permLattice_of_mem hw, fold_permLattice]
  change _ = (v i0 + v i1 + v i3) • fold (w • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ)) +
    v i2 • fold (w • (Pi.single i2 1 : Fin TwistTag.D4.tag.rank → ℤ))
  rw [add_smul, add_smul]
  abel

@[expose] def weylCands : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((1, 0), (0, 1)), ((2, 1), (-3, -1)), ((2, 1), (-3, -2)), ((-2, -1), (3, 1)),
    ((-2, -1), (3, 2)), ((-1, -1), (0, 1)), ((-1, -1), (3, 2)), ((1, 1), (-3, -2)),
    ((1, 1), (0, -1)), ((-1, 0), (3, 1)), ((-1, 0), (0, -1)), ((1, 0), (-3, -1))]

theorem weylCands_check : ∀ X ∈ g2FoldRoots, ∀ Y ∈ g2FoldRoots,
    (applyP (X, Y) (1, 1) ∈ g2FoldRoots ∧ applyP (X, Y) (2, 1) ∈ g2FoldRoots ∧
      applyP (X, Y) (3, 1) ∈ g2FoldRoots ∧ applyP (X, Y) (3, 2) ∈ g2FoldRoots) →
      (X, Y) ∈ weylCands := by decide

theorem foldPair_mem {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4) :
    foldPair w ∈ weylCands := by
  have hX := fold_mem_of_isRoot (IsRoot.smul (isRoot_single TwistTag.D4.tag i0) w)
  have hY := fold_mem_of_isRoot (IsRoot.smul (isRoot_single TwistTag.D4.tag i2) w)
  have key : ∀ v : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag v →
      applyP (foldPair w) (fold v) ∈ g2FoldRoots := fun v hv => by
    rw [← fold_smul hw]
    exact fold_mem_of_isRoot (IsRoot.smul hv w)
  exact weylCands_check _ hX _ hY
    ⟨key ![1, 0, 1, 0] (isRoot_iff_mem_artifactRoots.2 (by decide)),
      key ![1, 1, 1, 0] (isRoot_iff_mem_artifactRoots.2 (by decide)),
      key ![1, 1, 1, 1] (isRoot_iff_mem_artifactRoots.2 (by decide)),
      key ![1, 1, 2, 1] (isRoot_iff_mem_artifactRoots.2 (by decide))⟩

theorem eq_one_of_foldPair {u : WeylGroup TwistTag.D4.tag} (hu : u ∈ relWeylTwist TwistTag.D4)
    (h : foldPair u = ((1, 0), (0, 1))) : u = 1 := by
  have h0 : fold (u • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
      fold (Pi.single i0 1) := by
    rw [fold_single0]
    exact congrArg Prod.fst h
  have h2 : fold (u • (Pi.single i2 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
      fold (Pi.single i2 1) := by
    rw [fold_single2]
    exact congrArg Prod.snd h
  have ht0 := TwistTag.D4.height_of_mem_diagramOrbit (mem_diagramOrbit_of_fold_eq
    (isRoot_single _ i0) (IsRoot.smul (isRoot_single _ i0) u) h0)
  have ht2 := TwistTag.D4.height_of_mem_diagramOrbit (mem_diagramOrbit_of_fold_eq
    (isRoot_single _ i2) (IsRoot.smul (isRoot_single _ i2) u) h2)
  have ht1 : height (u • (Pi.single i1 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
      height (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    rw [single_i1_eq, smul_permLattice_of_mem hu, height_permLattice, ht0]
  have ht3 : height (u • (Pi.single i3 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
      height (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    rw [single_i3_eq, smul_permLattice_of_mem hu, smul_permLattice_of_mem hu, height_permLattice,
      height_permLattice, ht0]
  refine eq_one_of_forall_height_pos fun i => ?_
  rcases fin_cases i with rfl | rfl | rfl | rfl
  · rw [ht0]; decide
  · rw [ht1]; decide
  · rw [ht2]; decide
  · rw [ht3]; decide

theorem foldPair_injective {w w' : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (hw' : w' ∈ relWeylTwist TwistTag.D4) (h : foldPair w = foldPair w') : w = w' := by
  have hu : w'⁻¹ * w ∈ relWeylTwist TwistTag.D4 := mul_mem (inv_mem hw') hw
  have key : ∀ i : Fin TwistTag.D4.tag.rank,
      fold (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
        fold (w' • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) →
      fold ((w'⁻¹ * w) • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) =
        fold (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) := fun i hi => by
    rw [mul_smul, fold_smul (inv_mem hw'), hi, ← fold_smul (inv_mem hw'), inv_smul_smul]
  have h1 : w'⁻¹ * w = 1 := eq_one_of_foldPair hu (by
    simp only [foldPair]
    rw [key i0 (congrArg Prod.fst h), key i2 (congrArg Prod.snd h), fold_single0, fold_single2])
  exact (inv_mul_eq_one.1 h1).symm

theorem weylCands_classify : ∀ P ∈ weylCands, P = ((1, 0), (0, 1)) ∨
    (P.1 - (1, 0)).1 * (P.2 - (0, 1)).2 - (P.1 - (1, 0)).2 * (P.2 - (0, 1)).1 ∈
      ([1, -1, 3, -3, 4, -4] : List ℤ) ∨
    (P ≠ ((-1, 0), (0, -1)) ∧ ∃ μ ∈ g2FoldRoots, applyP P μ = -μ) := by decide

theorem weylCands_refl_unique : ∀ P ∈ weylCands, ∀ Q ∈ weylCands, ∀ μ ∈ g2FoldRoots,
    (P ≠ ((1, 0), (0, 1)) ∧ Q ≠ ((1, 0), (0, 1)) ∧ P ≠ ((-1, 0), (0, -1)) ∧
      Q ≠ ((-1, 0), (0, -1)) ∧ applyP P μ = -μ ∧ applyP Q μ = -μ) → P = Q := by decide

section Character

variable {K : Type} [Field K] {a : Fin TwistTag.D4.tag.rank → Kˣ} {A B : Kˣ}
  (h0 : a i0 = A) (h1 : a i1 = A) (h2 : a i2 = B) (h3 : a i3 = A) {p : ℕ} (hp : p.Prime)
  (hp3 : 3 < p) (hA : A ^ p = 1) (hB : B ^ p = 1) (hAB : ¬(A = 1 ∧ B = 1))

include h0 h1 h2 h3 in
theorem mem_rootCharKernel_iff {α : Fin TwistTag.D4.tag.rank → ℤ} :
    α ∈ rootCharKernel a ↔ IsRoot TwistTag.D4.tag α ∧ foldChar A B (fold α) = 1 := by
  rw [rootCharKernel, Set.mem_ofPred_eq, rootChar_eq_foldChar h0 h1 h2 h3]

theorem foldChar_sub (μ ν : ℤ × ℤ) :
    foldChar A B (μ - ν) = foldChar A B μ * (foldChar A B ν)⁻¹ := by
  rw [sub_eq_add_neg, foldChar_add, foldChar_neg]

include hA hB in
theorem foldChar_pow_eq_one (μ : ℤ × ℤ) : foldChar A B μ ^ p = 1 := by
  rw [foldChar, mul_pow, ← zpow_natCast, ← zpow_natCast (B ^ μ.2), ← zpow_mul, ← zpow_mul,
    mul_comm μ.1, mul_comm μ.2, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hA, hB, one_zpow,
    one_zpow, one_mul]

include hp hp3 hA hB hAB in
theorem false_of_det {x y : ℤ × ℤ} (hx : foldChar A B x = 1) (hy : foldChar A B y = 1)
    (hd0 : x.1 * y.2 - x.2 * y.1 ≠ 0) (hd4 : (x.1 * y.2 - x.2 * y.1).natAbs ≤ 4) : False := by
  obtain ⟨hAd, hBd⟩ := foldChar_det hx hy
  have hp5 := five_le_of_prime_of_three_lt hp hp3
  have hnd : ¬ (p : ℤ) ∣ (x.1 * y.2 - x.2 * y.1) := not_dvd_of_natAbs_lt hd0 (by omega)
  exact hAB ⟨eq_one_of_pow_prime_of_zpow hp hA hAd hnd, eq_one_of_pow_prime_of_zpow hp hB hBd hnd⟩

include hp hp3 hA hB hAB in
theorem fold_eq_or_neg {μ ν : ℤ × ℤ} (hμ : μ ∈ g2FoldRoots) (hν : ν ∈ g2FoldRoots)
    (hμ1 : foldChar A B μ = 1) (hν1 : foldChar A B ν = 1) : ν = μ ∨ ν = -μ := by
  rcases det_check μ hμ ν hν with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    refine false_of_det hp hp3 hA hB hAB hμ1 hν1 ?_ ?_ <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

include hp hp3 hA hB in
theorem foldChar_eq_one_of_neg {μ : ℤ × ℤ} (h : foldChar A B (-μ) = foldChar A B μ) :
    foldChar A B μ = 1 := by
  rw [foldChar_neg] at h
  have h2 : foldChar A B μ ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel _
  have hp5 := five_le_of_prime_of_three_lt hp hp3
  exact eq_one_of_pow_prime_of_zpow hp (foldChar_pow_eq_one hA hB μ) h2
    (not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega))

include h0 h1 h2 h3 in
theorem foldChar_foldPair_sub {w : WeylGroup TwistTag.D4.tag} (hwa : w ∈ rootCharStabilizer a)
    (i : Fin TwistTag.D4.tag.rank) :
    foldChar A B (fold (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) -
      fold (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) = 1 := by
  have h := hwa (Pi.single i 1)
  rw [rootChar_eq_foldChar h0 h1 h2 h3, rootChar_eq_foldChar h0 h1 h2 h3] at h
  rw [foldChar_sub, h, mul_inv_cancel]

theorem fold_comb (μ : ℤ × ℤ) :
    fold (μ.1 • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) + μ.2 • Pi.single i2 1) = μ := by
  rw [fold_add, fold_zsmul, fold_zsmul, fold_single0, fold_single2]
  ext <;> simp

include h0 h1 h2 h3 hp hp3 hA hB hAB in
theorem foldPair_cases_of_stabilizer {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (hwa : w ∈ rootCharStabilizer a) :
    w = 1 ∨ (foldPair w ≠ ((1, 0), (0, 1)) ∧ foldPair w ≠ ((-1, 0), (0, -1)) ∧
      ∃ μ ∈ g2FoldRoots, applyP (foldPair w) μ = -μ ∧ foldChar A B μ = 1) := by
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  right
  have hid : foldPair w ≠ ((1, 0), (0, 1)) := fun h => hw1 (eq_one_of_foldPair hw h)
  rcases weylCands_classify _ (foldPair_mem hw) with hP | hdet | ⟨hneg, μ, hμ, hμneg⟩
  · exact absurd hP hid
  · exfalso
    have hx := foldChar_foldPair_sub h0 h1 h2 h3 hwa i0
    have hy := foldChar_foldPair_sub h0 h1 h2 h3 hwa i2
    rw [fold_single0] at hx
    rw [fold_single2] at hy
    simp only [foldPair, List.mem_cons, List.not_mem_nil, or_false] at hdet
    refine false_of_det hp hp3 hA hB hAB hx hy ?_ ?_ <;>
    · rcases hdet with h | h | h | h | h | h <;> rw [h] <;> decide
  · refine ⟨hid, hneg, μ, hμ, hμneg, foldChar_eq_one_of_neg hp hp3 hA hB ?_⟩
    have h := hwa (μ.1 • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) + μ.2 • Pi.single i2 1)
    rw [rootChar_eq_foldChar h0 h1 h2 h3, rootChar_eq_foldChar h0 h1 h2 h3, fold_smul hw,
      fold_comb, hμneg] at h
    exact h

include h0 h1 h2 h3 hp hp3 hA hB hAB in
theorem rootCharKernel_cases :
    rootCharKernel a = ∅ ∨ ∃ α, IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧
      rootCharKernel a = (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∪
        -(TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  rcases (rootCharKernel a).eq_empty_or_nonempty with h | ⟨β, hβ⟩
  · exact Or.inl h
  right
  obtain ⟨hβr, hβ1⟩ := (mem_rootCharKernel_iff h0 h1 h2 h3).1 hβ
  obtain ⟨α, hαr, hαpos, hα1⟩ : ∃ α, IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧
      foldChar A B (fold α) = 1 := by
    rcases lt_or_gt_of_ne hβr.height_ne_zero with hneg | hpos
    · refine ⟨-β, IsRoot.neg hβr, ?_, ?_⟩
      · rw [height_neg]
        omega
      · rw [fold_neg, foldChar_neg, hβ1, inv_one]
    · exact ⟨β, hβr, hpos, hβ1⟩
  refine ⟨α, hαr, hαpos, Set.ext fun γ => ?_⟩
  rw [mem_rootCharKernel_iff h0 h1 h2 h3, Set.mem_union, Set.mem_neg, Finset.mem_coe,
    Finset.mem_coe]
  constructor
  · rintro ⟨hγr, hγ1⟩
    rcases fold_eq_or_neg hp hp3 hA hB hAB (fold_mem_of_isRoot hαr) (fold_mem_of_isRoot hγr) hα1
      hγ1 with h | h
    · exact Or.inl (mem_diagramOrbit_of_fold_eq hαr hγr h)
    · exact Or.inr (mem_diagramOrbit_of_fold_eq hαr (IsRoot.neg hγr) (by rw [fold_neg, h, neg_neg]))
  · rintro (h | h)
    · exact ⟨TwistTag.D4.isRoot_of_mem_diagramOrbit hαr h,
        by rw [fold_eq_of_mem_diagramOrbit h, hα1]⟩
    · have hγ := IsRoot.neg (TwistTag.D4.isRoot_of_mem_diagramOrbit hαr h)
      rw [neg_neg] at hγ
      refine ⟨hγ, ?_⟩
      rw [← neg_neg γ, fold_neg, foldChar_neg, fold_eq_of_mem_diagramOrbit h, hα1, inv_one]

include h0 h1 h2 h3 hp hp3 hA hB hAB in
theorem rootCharStabilizer_cases {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (hwa : w ∈ rootCharStabilizer a) :
    w = 1 ∨ ((rootCharKernel a).Nonempty ∧ ∀ v ∈ relWeylTwist TwistTag.D4,
      ∀ b : Fin TwistTag.D4.foldedTag.rank, (∀ i ∈ TwistTag.D4.orbit b,
        v • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ rootCharKernel a) →
        w = v * TwistTag.D4.orbitReflection b * v⁻¹) := by
  rcases foldPair_cases_of_stabilizer h0 h1 h2 h3 hp hp3 hA hB hAB hw hwa with
    hw1 | ⟨hid, hneg, μ, hμ, hμneg, hμ1⟩
  · exact Or.inl hw1
  right
  obtain ⟨β, hβr, hβμ⟩ := exists_isRoot_fold_eq hμ
  refine ⟨⟨β, (mem_rootCharKernel_iff h0 h1 h2 h3).2 ⟨hβr, by rw [hβμ, hμ1]⟩⟩,
    fun v hv b hvb => ?_⟩
  have hi : TwistTag.D4.orbitMin b ∈ TwistTag.D4.orbit b := TwistTag.D4.orbitMin_mem b
  obtain ⟨hvr, hv1⟩ := (mem_rootCharKernel_iff h0 h1 h2 h3).1 (hvb _ hi)
  set μ₀ := fold (v • (Pi.single (TwistTag.D4.orbitMin b) 1 : Fin TwistTag.D4.tag.rank → ℤ))
    with hμ₀def
  have hμ₀ : μ₀ ∈ g2FoldRoots := fold_mem_of_isRoot hvr
  have hwμ₀ : applyP (foldPair w) μ₀ = -μ₀ := by
    rcases fold_eq_or_neg hp hp3 hA hB hAB hμ hμ₀ hμ1 hv1 with h | h
    · rw [h, hμneg]
    · rw [h, applyP_neg, hμneg, neg_neg]
  set x := v * TwistTag.D4.orbitReflection b * v⁻¹ with hx
  have hxW : x ∈ relWeylTwist TwistTag.D4 :=
    mul_mem (mul_mem hv (TwistTag.D4.orbitReflection_mem b)) (inv_mem hv)
  have hxa : x ∈ rootCharStabilizer a := by
    refine kernelReflectionGroup_le a ?_
    rw [hx, ← MulAut.conj_apply, TwistTag.orbitReflection, CoxeterSystem.wordProd,
      map_list_prod]
    refine list_prod_mem fun y hy => ?_
    rw [List.map_map, List.mem_map] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact Subgroup.subset_closure
      ⟨v, j, hvb j ((TwistTag.D4.mem_orbitWord).1 hj), MulAut.conj_apply _ _⟩
  have hx1 : x ≠ 1 := fun h => TwistTag.D4.orbitReflection_ne_one b
    (mul_eq_left.1 (mul_inv_eq_one.1 h))
  rcases foldPair_cases_of_stabilizer h0 h1 h2 h3 hp hp3 hA hB hAB hxW hxa with
    hx1' | ⟨hxid, hxneg, -⟩
  · exact absurd hx1' hx1
  have hxμ₀ : applyP (foldPair x) μ₀ = -μ₀ := by
    rw [hμ₀def, ← fold_smul hxW, hx, mul_smul, mul_smul, inv_smul_smul,
      TwistTag.D4.orbitReflection_smul_single hi, smul_neg, fold_neg]
  exact foldPair_injective hw hxW (weylCands_refl_unique _ (foldPair_mem hw) _
    (foldPair_mem hxW) μ₀ hμ₀ ⟨hid, hxid, hneg, hxneg, hwμ₀, hxμ₀⟩)

end Character

end TrialityFold

end CFSG.RankThree.Chevalley
