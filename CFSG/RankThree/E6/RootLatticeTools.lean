module

public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.RelativeWeylTwist

public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def weylMatrix (w : WeylGroup τ) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  Matrix.of fun i j => (w • (Pi.single j 1 : Fin τ.rank → ℤ)) i

theorem weylMatrix_apply (w : WeylGroup τ) (i j : Fin τ.rank) :
    weylMatrix w i j = (w • (Pi.single j 1 : Fin τ.rank → ℤ)) i :=
  rfl

theorem weylMatrix_eq_toMatrix' (w : WeylGroup τ) :
    weylMatrix w =
      LinearMap.toMatrix' (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w) := by
  ext i j
  rw [weylMatrix_apply, LinearMap.toMatrix'_apply, smul_def]

theorem weylMatrix_mulVec (w : WeylGroup τ) (x : Fin τ.rank → ℤ) :
    (weylMatrix w).mulVec x = w • x := by
  rw [weylMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec, smul_def]

theorem weylMatrix_one : weylMatrix (1 : WeylGroup τ) = 1 := by
  ext i j
  rw [weylMatrix_apply, one_smul, Matrix.one_apply, Pi.single_apply]

theorem weylMatrix_mul (w w' : WeylGroup τ) :
    weylMatrix (w * w') = weylMatrix w * weylMatrix w' := by
  ext i j
  rw [weylMatrix_apply, mul_smul, ← weylMatrix_mulVec w', ← weylMatrix_mulVec w,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

@[expose] def weylMatrixHom (τ : Tag) : WeylGroup τ →* Matrix (Fin τ.rank) (Fin τ.rank) ℤ where
  toFun := weylMatrix
  map_one' := weylMatrix_one
  map_mul' := weylMatrix_mul

theorem weylMatrix_pow (w : WeylGroup τ) (n : ℕ) : weylMatrix (w ^ n) = weylMatrix w ^ n :=
  map_pow (weylMatrixHom τ) w n

theorem weylMatrix_injective : Function.Injective (weylMatrix (τ := τ)) := by
  intro w w' h
  refine ext_single fun i => ?_
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, h]

theorem eq_of_smul_single_eq {w w' : WeylGroup τ}
    (h : ∀ j, w • (Pi.single j 1 : Fin τ.rank → ℤ) = w' • (Pi.single j 1 : Fin τ.rank → ℤ)) :
    w = w' :=
  ext_single h

variable (R : Type*) [CommRing R]

@[expose] def dualMatrix (w : WeylGroup τ) : Matrix (Fin τ.rank) (Fin τ.rank) R :=
  ((weylMatrix w).map (Int.cast : ℤ → R)).transpose

variable {R}

@[expose] def charVal (z : Fin τ.rank → R) (x : Fin τ.rank → ℤ) : R :=
  ∑ i, (x i : R) * z i

theorem charVal_add (z : Fin τ.rank → R) (x y : Fin τ.rank → ℤ) :
    charVal z (x + y) = charVal z x + charVal z y := by
  simp only [charVal, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

theorem charVal_neg (z : Fin τ.rank → R) (x : Fin τ.rank → ℤ) :
    charVal z (-x) = -charVal z x := by
  simp only [charVal, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem charVal_smul (z : Fin τ.rank → R) (c : ℤ) (x : Fin τ.rank → ℤ) :
    charVal z (c • x) = c * charVal z x := by
  simp only [charVal, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_assoc, Finset.mul_sum]

theorem charVal_single (z : Fin τ.rank → R) (j : Fin τ.rank) :
    charVal z (Pi.single j 1) = z j := by
  rw [charVal, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem charVal_mulVec (z : Fin τ.rank → R) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (x : Fin τ.rank → ℤ) :
    charVal ((M.map (Int.cast : ℤ → R)).transpose.mulVec z) x = charVal z (M.mulVec x) := by
  simp only [charVal, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
    Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem charVal_dualMatrix (z : Fin τ.rank → R) (w : WeylGroup τ) (x : Fin τ.rank → ℤ) :
    charVal ((dualMatrix R w).mulVec z) x = charVal z (w • x) := by
  rw [dualMatrix, charVal_mulVec, weylMatrix_mulVec]

theorem dualMatrix_mul (w w' : WeylGroup τ) :
    dualMatrix R (w * w') = dualMatrix R w' * dualMatrix R w := by
  rw [dualMatrix, dualMatrix, dualMatrix, weylMatrix_mul,
    show (Int.cast : ℤ → R) = ⇑(Int.castRingHom R) from rfl, Matrix.map_mul,
    Matrix.transpose_mul]

theorem dualMatrix_one : dualMatrix R (1 : WeylGroup τ) = 1 := by
  rw [dualMatrix, weylMatrix_one, Matrix.map_one _ Int.cast_zero Int.cast_one,
    Matrix.transpose_one]

theorem charVal_smul_col (a : R) (z : Fin τ.rank → R) (x : Fin τ.rank → ℤ) :
    charVal (a • z) x = a * charVal z x := by
  simp only [charVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem charVal_mulVec_of_eigen {z : Fin τ.rank → R} {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    {c : R} (hz : ((M.map (Int.cast : ℤ → R)).transpose).mulVec z = c • z)
    (x : Fin τ.rank → ℤ) : charVal z (M.mulVec x) = c * charVal z x := by
  rw [← charVal_mulVec, hz, charVal_smul_col]

theorem charVal_pow_mulVec_of_eigen {z : Fin τ.rank → R} {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    {c : R} (hz : ((M.map (Int.cast : ℤ → R)).transpose).mulVec z = c • z) (n : ℕ)
    (x : Fin τ.rank → ℤ) : charVal z ((M ^ n).mulVec x) = c ^ n * charVal z x := by
  induction n generalizing x with
  | zero => rw [pow_zero, Matrix.one_mulVec, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, charVal_mulVec_of_eigen hz, pow_succ, mul_assoc]

theorem charVal_mulVec_eq_sum (z : Fin τ.rank → R) (B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (c : Fin τ.rank → ℤ) :
    charVal z (B.mulVec c) = ∑ j, (c j : R) * charVal z (fun i => B i j) := by
  simp only [charVal, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem eq_zero_of_charVal_columns {z : Fin τ.rank → R} {B B' : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hB : B * B' = 1) (h : ∀ j, charVal z (fun i => B i j) = 0) : z = 0 := by
  funext j
  rw [Pi.zero_apply, ← charVal_single z j]
  have e : (Pi.single j 1 : Fin τ.rank → ℤ) = B.mulVec (B'.mulVec (Pi.single j 1)) := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  rw [e, charVal_mulVec_eq_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [h k, mul_zero]

theorem eq_of_charVal_single {z z' : Fin τ.rank → R}
    (h : ∀ j, charVal z (Pi.single j 1) = charVal z' (Pi.single j 1)) : z = z' := by
  funext j
  rw [← charVal_single z j, ← charVal_single z' j, h]

@[expose] def detLaplace : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | n + 1, A => ∑ j : Fin (n + 1),
      (-1) ^ (j : ℕ) * A 0 j * detLaplace n (A.submatrix Fin.succ j.succAbove)

theorem detLaplace_eq_det : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    detLaplace n A = A.det
  | 0, A => by rw [detLaplace.eq_1, Matrix.det_isEmpty]
  | n + 1, A => by
    rw [detLaplace.eq_2, Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [detLaplace_eq_det n]

@[expose] def chainRoot {n : ℕ} (ι : Fin n → Fin τ.rank) (i j : Fin (n + 1)) :
    Fin τ.rank → ℤ :=
  fun l => ∑ k : Fin n,
    ((if (i : ℕ) ≤ k ∧ (k : ℕ) < j then 1 else 0) -
        (if (j : ℕ) ≤ k ∧ (k : ℕ) < i then 1 else 0)) * (if ι k = l then 1 else 0)

theorem chainRoot_self {n : ℕ} (ι : Fin n → Fin τ.rank) (i : Fin (n + 1)) :
    chainRoot ι i i = 0 := by
  funext l
  simp only [chainRoot, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [sub_self, zero_mul]

theorem chainRoot_swap {n : ℕ} (ι : Fin n → Fin τ.rank) (i j : Fin (n + 1)) :
    chainRoot ι j i = -chainRoot ι i j := by
  funext l
  simp only [chainRoot, Pi.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

@[expose] def IsPositiveTransition {n : ℕ} (T : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (ι ι' : Fin n → Fin τ.rank) : Prop :=
  ∃ π : Equiv.Perm (Fin (n + 1)), ∀ i j, T (chainRoot ι i j) = chainRoot ι' (π i) (π j)

@[expose] def IsNegativeTransition {n : ℕ} (T : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (ι ι' : Fin n → Fin τ.rank) : Prop :=
  ∃ π : Equiv.Perm (Fin (n + 1)), ∀ i j, T (chainRoot ι i j) = chainRoot ι' (π j) (π i)

@[expose] def e6Index (i : Fin 6) : Fin Tag.E6.rank := i

@[expose] def e6Word (l : List (Fin 6)) : List (Fin Tag.E6.rank) := l

@[expose] def e6Rho : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

@[expose] def rhoMatrix : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.of fun i j => if j = e6Rho.symm i then 1 else 0

theorem permLattice_eq_mulVec (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Rho x = rhoMatrix.mulVec x := by
  funext i
  simp [permLattice, rhoMatrix, Matrix.mulVec, dotProduct]

@[expose] def e6RootVec (m : Fin 72) : Fin Tag.E6.rank → ℤ := e6Certificate.root m

theorem length_e6Certificate_roots : e6Certificate.roots.length = 72 := by decide

theorem isRoot_e6RootVec (m : Fin 72) : IsRoot Tag.E6 (e6RootVec m) :=
  RootCertificate.isRoot_root e6Certificate_check m (by rw [length_e6Certificate_roots]; exact m.2)

theorem isRoot_iff_exists_e6RootVec {v : Fin Tag.E6.rank → ℤ} :
    IsRoot Tag.E6 v ↔ ∃ m : Fin 72, e6RootVec m = v := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => hm ▸ isRoot_e6RootVec m⟩
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq e6Certificate_check h
  exact ⟨⟨k, length_e6Certificate_roots ▸ hk⟩, rfl⟩

theorem wordProd_e6Word_smul (ω : List (Fin 6)) (v : Fin Tag.E6.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd (e6Word ω) • v = (e6Word ω).foldr (reflect Tag.E6) v :=
  wordProd_smul _ v

theorem weylMatrix_wordProd_e6 {ω : List (Fin 6)} {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (h : ∀ j : Fin 6, (e6Word ω).foldr (reflect Tag.E6) (Pi.single (e6Index j) 1) =
      fun i => M i (e6Index j)) :
    weylMatrix ((coxeterSystem Tag.E6).wordProd (e6Word ω)) = M := by
  ext i j
  rw [weylMatrix_apply, wordProd_e6Word_smul]
  exact congrFun (h j) i

theorem image_smul_parabolicRoots_eq {w : WeylGroup Tag.E6} {J J' : Set (Fin Tag.E6.rank)}
    {P P' : Fin Tag.E6.rank → Prop} (hJ : ∀ i, i ∈ J ↔ P i) (hJ' : ∀ i, i ∈ J' ↔ P' i)
    (h₁ : ∀ m : Fin 72, (∀ i, ¬P i → e6RootVec m i = 0) → ∀ i, ¬P' i → (w • e6RootVec m) i = 0)
    (h₂ : ∀ m : Fin 72, (∀ i, ¬P' i → e6RootVec m i = 0) →
      ∃ m' : Fin 72, (∀ i, ¬P i → e6RootVec m' i = 0) ∧ w • e6RootVec m' = e6RootVec m) :
    (w • ·) '' parabolicRoots Tag.E6 J = parabolicRoots Tag.E6 J' := by
  ext β
  simp only [Set.mem_image, parabolicRoots, Set.mem_ofPred_eq, hJ, hJ']
  constructor
  · rintro ⟨α, ⟨hα, hsupp⟩, rfl⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    exact ⟨IsRoot.smul hα w, h₁ m hsupp⟩
  · rintro ⟨hβ, hsupp⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hβ
    obtain ⟨m', hm', he⟩ := h₂ m hsupp
    exact ⟨e6RootVec m', ⟨isRoot_e6RootVec m', hm'⟩, he⟩

theorem image_wordProd_parabolicRoots_eq {ω : List (Fin 6)} {J J' : Set (Fin Tag.E6.rank)}
    {P P' : Fin Tag.E6.rank → Prop} (hJ : ∀ i, i ∈ J ↔ P i) (hJ' : ∀ i, i ∈ J' ↔ P' i)
    (h₁ : ∀ m : Fin 72, (∀ i, ¬P i → e6RootVec m i = 0) →
      ∀ i, ¬P' i → (e6Word ω).foldr (reflect Tag.E6) (e6RootVec m) i = 0)
    (h₂ : ∀ m : Fin 72, (∀ i, ¬P' i → e6RootVec m i = 0) →
      ∃ m' : Fin 72, (∀ i, ¬P i → e6RootVec m' i = 0) ∧
        (e6Word ω).foldr (reflect Tag.E6) (e6RootVec m') = e6RootVec m) :
    ((coxeterSystem Tag.E6).wordProd (e6Word ω) • ·) '' parabolicRoots Tag.E6 J =
      parabolicRoots Tag.E6 J' := by
  refine image_smul_parabolicRoots_eq hJ hJ' (fun m hm i hi => ?_) (fun m hm => ?_)
  · rw [wordProd_e6Word_smul]
    exact h₁ m hm i hi
  · obtain ⟨m', hm', he⟩ := h₂ m hm
    exact ⟨m', hm', by rw [wordProd_e6Word_smul]; exact he⟩

theorem wordProd_conj_e6 (ω ω' : List (Fin 6)) :
    (coxeterSystem Tag.E6).wordProd (e6Word ω) * (coxeterSystem Tag.E6).wordProd (e6Word ω') *
        ((coxeterSystem Tag.E6).wordProd (e6Word ω))⁻¹ =
      (coxeterSystem Tag.E6).wordProd (e6Word (ω ++ ω' ++ ω.reverse)) := by
  rw [← CoxeterSystem.wordProd_reverse, ← CoxeterSystem.wordProd_append,
    ← CoxeterSystem.wordProd_append]
  rfl

theorem e6RootVec_injective : Function.Injective e6RootVec := by
  intro m m' h
  revert m m'
  decide +kernel

theorem ncard_parabolicRoots_eq {J : Set (Fin Tag.E6.rank)} {P : Fin Tag.E6.rank → Prop}
    [DecidablePred P] (hJ : ∀ i, i ∈ J ↔ P i) {n : ℕ}
    (h : (Finset.univ.filter fun m : Fin 72 => ∀ i, ¬P i → e6RootVec m i = 0).card = n) :
    (parabolicRoots Tag.E6 J).ncard = n := by
  have e : parabolicRoots Tag.E6 J =
      e6RootVec '' ↑(Finset.univ.filter fun m : Fin 72 => ∀ i, ¬P i → e6RootVec m i = 0) := by
    ext α
    simp only [parabolicRoots, Set.mem_ofPred_eq, hJ, Set.mem_image, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hα, hs⟩
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
      exact ⟨m, hs, rfl⟩
    · rintro ⟨m, hs, rfl⟩
      exact ⟨isRoot_e6RootVec m, hs⟩
  rw [e, Set.ncard_image_of_injective _ e6RootVec_injective, Set.ncard_coe_finset, h]

@[expose] def restrictMatrix₂ (w : WeylGroup τ) (j j' : Fin τ.rank) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![weylMatrix w j j, weylMatrix w j j'; weylMatrix w j' j, weylMatrix w j' j']

@[expose] def support134 : Set (Fin Tag.E6.rank) := {e6Index 0, e6Index 2, e6Index 3}

theorem mem_support134 (i : Fin Tag.E6.rank) :
    i ∈ support134 ↔ (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 3) := by
  simp only [support134, Set.mem_insert_iff, Set.mem_singleton_iff]

@[expose] def chain134 : Fin 3 → Fin Tag.E6.rank := ![e6Index 0, e6Index 2, e6Index 3]

@[expose] def support13 : Set (Fin Tag.E6.rank) := {e6Index 0, e6Index 2}

@[expose] def support56 : Set (Fin Tag.E6.rank) := {e6Index 4, e6Index 5}

@[expose] def chain13 : Fin 2 → Fin Tag.E6.rank := ![e6Index 0, e6Index 2]

@[expose] def chain56 : Fin 2 → Fin Tag.E6.rank := ![e6Index 4, e6Index 5]

theorem mem_support13 (i : Fin Tag.E6.rank) : i ∈ support13 ↔ (i = e6Index 0 ∨ i = e6Index 2) := by
  simp only [support13, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem mem_support56 (i : Fin Tag.E6.rank) : i ∈ support56 ↔ (i = e6Index 4 ∨ i = e6Index 5) := by
  simp only [support56, Set.mem_insert_iff, Set.mem_singleton_iff]

@[expose] def rootKernel (z : Fin Tag.E6.rank → R) : Set (Fin Tag.E6.rank → ℤ) :=
  {α | IsRoot Tag.E6 α ∧ charVal z α = 0}

theorem mem_rootKernel {z : Fin Tag.E6.rank → R} {α : Fin Tag.E6.rank → ℤ} :
    α ∈ rootKernel z ↔ IsRoot Tag.E6 α ∧ charVal z α = 0 :=
  Iff.rfl

end CFSG.RankThree.E6
