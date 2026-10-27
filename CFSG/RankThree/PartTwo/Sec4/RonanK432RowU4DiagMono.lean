module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432.U4Diag

@[expose] def psi {K : Type} [Monoid K] (ω : K) (x : ZMod 3) : K := ω ^ x.val

theorem psi_zero {K : Type} [Monoid K] (ω : K) : psi ω 0 = 1 := by
  simp [psi]

theorem psi_add {K : Type} [Field K] {ω : K} (hω : IsPrimitiveRoot ω 3) (x y : ZMod 3) :
    psi ω (x + y) = psi ω x * psi ω y := by
  have h3 : orderOf ω = 3 := hω.eq_orderOf.symm
  have key := pow_mod_orderOf ω (x.val + y.val)
  rw [h3] at key
  unfold psi
  rw [← pow_add, ZMod.val_add]
  exact key

theorem psi_injective {K : Type} [Field K] {ω : K} (hω : IsPrimitiveRoot ω 3) :
    Function.Injective (psi ω) := by
  intro x y hxy
  have h := hω.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) hxy
  exact ZMod.val_injective 3 h

theorem psi_pow {K : Type} [Field K] {ω : K} (hω : IsPrimitiveRoot ω 3) (x : ZMod 3) (n : ℕ) :
    psi ω x ^ n = psi ω ((n : ZMod 3) * x) := by
  induction n with
  | zero => simp [psi_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← psi_add hω]
    congr 1
    push_cast
    ring

theorem psi_prod {K : Type} [Field K] {ω : K} (hω : IsPrimitiveRoot ω 3) {ι : Type}
    [DecidableEq ι] (s : Finset ι) (a : ι → ZMod 3) :
    ∏ i ∈ s, psi ω (a i) = psi ω (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simp [psi_zero]
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, psi_add hω]

theorem psi_eq_one_iff {K : Type} [Field K] {ω : K} (hω : IsPrimitiveRoot ω 3) (x : ZMod 3) :
    psi ω x = 1 ↔ x = 0 := by
  rw [← psi_zero ω]
  exact (psi_injective hω).eq_iff

theorem sub_const_of_psi_eq {K : Type} [Field K] {ω : K} (hω : IsPrimitiveRoot ω 3) {ι : Type}
    (σ : ι → ι) (a : ι → ZMod 3) (n : ℕ) (u : K)
    (h : ∀ l, psi ω (a (σ l)) = u * psi ω (a l) ^ n) (l l' : ι) :
    a (σ l) - (n : ZMod 3) * a l = a (σ l') - (n : ZMod 3) * a l' := by
  have e2 : psi ω (a (σ l) + (n : ZMod 3) * a l') = psi ω (a (σ l') + (n : ZMod 3) * a l) := by
    rw [psi_add hω, psi_add hω, ← psi_pow hω, ← psi_pow hω, h l, h l']
    ring
  have e3 := psi_injective hω e2
  linear_combination e3

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def mono {K : Type} [Zero K] (σ : Equiv.Perm ι) (ε : ι → K) : Matrix ι ι K :=
  Matrix.of fun r c => if r = σ c then ε c else 0

theorem mono_apply {K : Type} [Zero K] (σ : Equiv.Perm ι) (ε : ι → K) (r c : ι) :
    mono σ ε r c = if r = σ c then ε c else 0 :=
  rfl

theorem mono_mul_diagonal_mul_transpose {K : Type} [CommRing K] (σ : Equiv.Perm ι)
    (hσ : ∀ r, σ (σ r) = r) (ε d : ι → K) (hε : ∀ c, ε c * ε c = 1) :
    mono σ ε * diagonal d * (mono σ ε)ᵀ = diagonal (fun r => d (σ r)) := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ r)]
  · have h1 : mono σ ε r (σ r) = ε (σ r) := by simp [mono_apply, hσ]
    have h2 : mono σ ε c (σ r) = if c = r then ε (σ r) else 0 := by
      simp [mono_apply, hσ]
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, h1, h2, Matrix.diagonal_apply]
    by_cases hrc : c = r
    · subst hrc
      simp only [if_true]
      linear_combination d (σ c) * hε (σ c)
    · simp [hrc, Ne.symm hrc]
  · intro s _ hs
    have hne : r ≠ σ s := fun h => hs (by rw [h, hσ])
    simp [Matrix.mul_diagonal, mono_apply, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem transpose_mono_mul_mono {K : Type} [CommRing K] (σ : Equiv.Perm ι)
    (hσ : ∀ r, σ (σ r) = r) (ε : ι → K) (hε : ∀ c, ε c * ε c = 1) :
    (mono σ ε)ᵀ * mono σ ε = 1 := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ r)]
  · by_cases hrc : r = c
    · subst hrc
      simp [mono_apply, hε]
    · have hne : σ r ≠ σ c := fun h => hrc (by rw [← hσ r, h, hσ])
      simp [mono_apply, hne, hrc]
  · intro s _ hs
    simp [mono_apply, Matrix.transpose_apply, hs]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mono_mul_transpose {K : Type} [CommRing K] (σ : Equiv.Perm ι)
    (hσ : ∀ r, σ (σ r) = r) (ε : ι → K) (hε : ∀ c, ε c * ε c = 1) :
    mono σ ε * (mono σ ε)ᵀ = 1 := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ r)]
  · by_cases hrc : r = c
    · subst hrc
      simp [mono_apply, hσ, hε]
    · simp [mono_apply, hσ, Matrix.transpose_apply, hrc, Ne.symm hrc]
  · intro s _ hs
    have hne : r ≠ σ s := fun h => hs (by rw [h, hσ])
    simp [mono_apply, Matrix.transpose_apply, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem map_mono {K : Type} [Semiring K] (f : K →+* K) (σ : Equiv.Perm ι)
    (ε : ι → K) (hf : ∀ c, f (ε c) = ε c) :
    (mono σ ε).map f = mono σ ε := by
  ext r c
  simp only [Matrix.map_apply, mono_apply]
  split_ifs
  · exact hf c
  · exact map_zero f

theorem det_mono {K : Type} [CommRing K] (σ : Equiv.Perm ι) (hσ : ∀ r, σ (σ r) = r)
    (ε : ι → K) : (mono σ ε).det = ((Equiv.Perm.sign σ : ℤˣ) : K) * ∏ c, ε c := by
  have h : mono σ ε = (1 : Matrix ι ι K).submatrix σ id * diagonal ε := by
    ext r c
    rw [Matrix.mul_diagonal, mono_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    by_cases hrc : r = σ c
    · subst hrc
      simp [hσ]
    · have : σ r ≠ c := fun h' => hrc (by rw [← h', hσ])
      simp [hrc, this]
  rw [h, Matrix.det_mul, Matrix.det_permute, Matrix.det_one, Matrix.det_diagonal, mul_one]

@[expose] def monoUnit {K : Type} [CommRing K] (σ : Equiv.Perm ι) (hσ : ∀ r, σ (σ r) = r)
    (ε : ι → K) (hε : ∀ c, ε c * ε c = 1) : Matrix.GeneralLinearGroup ι K :=
  ⟨mono σ ε, (mono σ ε)ᵀ, mono_mul_transpose σ hσ ε hε, transpose_mono_mul_mono σ hσ ε hε⟩

theorem monoUnit_val {K : Type} [CommRing K] (σ : Equiv.Perm ι) (hσ : ∀ r, σ (σ r) = r)
    (ε : ι → K) (hε : ∀ c, ε c * ε c = 1) :
    ((monoUnit σ hσ ε hε : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = mono σ ε :=
  rfl

theorem monoUnit_inv_val {K : Type} [CommRing K] (σ : Equiv.Perm ι) (hσ : ∀ r, σ (σ r) = r)
    (ε : ι → K) (hε : ∀ c, ε c * ε c = 1) :
    (((monoUnit σ hσ ε hε)⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = (mono σ ε)ᵀ :=
  rfl

end CFSG.RankThree.PartTwo.Sec4.RonanK432.U4Diag

end
