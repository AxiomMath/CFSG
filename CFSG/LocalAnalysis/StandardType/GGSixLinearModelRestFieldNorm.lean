module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestFieldMono

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace LinModel

variable {m : ℕ} {F : Type} [Field F]

theorem map_map_ringAut (σ τ : F ≃+* F) (X : GL (Fin (m + 1)) F) :
    GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.map (τ : F →+* F) X) =
      GeneralLinearGroup.map ((σ * τ : F ≃+* F) : F →+* F) X := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply]
  rfl

theorem map_one_ringAut (X : GL (Fin (m + 1)) F) :
    GeneralLinearGroup.map ((1 : F ≃+* F) : F →+* F) X = X := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply]
  rfl

theorem map_scalar_ringAut (σ : F ≃+* F) (c : Fˣ) :
    GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.scalar (Fin (m + 1)) c) =
      GeneralLinearGroup.scalar (Fin (m + 1)) (Units.map (σ : F →* F) c) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    scalar_apply, scalar_apply, diagonal_apply, diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem isPermOf_map (σ : F ≃+* F) {X : GL (Fin (m + 1)) F} {π : Equiv.Perm (Fin (m + 1))}
    (h : IsPermOf (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) :
    IsPermOf ((GeneralLinearGroup.map (σ : F →+* F) X : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) π := by
  intro i l
  rw [GeneralLinearGroup.map_apply, ← h i l]
  exact map_ne_zero (σ : F →+* F)

theorem mul_apply_of_isPermOf {X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {πX πY : Equiv.Perm (Fin (m + 1))} (hY : IsPermOf Y πY) (i : Fin (m + 1)) :
    (X * Y) (πX (πY i)) i = X (πX (πY i)) (πY i) * Y (πY i) i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (πY i)]
  · intro k _ hk
    have h0 : Y k i = 0 := by
      by_contra h
      exact hk ((hY i k).mp h)
    rw [h0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem det_eq_prod_of_isPermOf [CharP F 2] {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {π : Equiv.Perm (Fin (m + 1))} (hA : IsPermOf A π) : A.det = ∏ i, A (π i) i := by
  rw [Matrix.det_apply, Finset.sum_eq_single π]
  · rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, CharTwo.neg_eq]
  · intro τ _ hτ
    obtain ⟨i, hi⟩ : ∃ i, τ i ≠ π i := by
      by_contra h
      push Not at h
      exact hτ (Equiv.ext h)
    have h0 : A (τ i) i = 0 := by
      by_contra h
      exact hi ((hA i (τ i)).mp h)
    have hz : ∏ k, A (τ k) k = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    simp [hz]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] noncomputable def twistNorm (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) :
    ℕ → GL (Fin (m + 1)) F
  | 0 => 1
  | k + 1 => A * GeneralLinearGroup.map (σ : F →+* F) (twistNorm A σ k)

theorem twistNorm_zero (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) : twistNorm A σ 0 = 1 := rfl

theorem twistNorm_succ (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) (k : ℕ) :
    twistNorm A σ (k + 1) = A * GeneralLinearGroup.map (σ : F →+* F) (twistNorm A σ k) := rfl

theorem conjAut_mul_fieldAut_pow (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) (k : ℕ) :
    (conjAut (m + 1) F A * fieldAut (m + 1) F σ) ^ k =
      conjAut (m + 1) F (twistNorm A σ k) * fieldAut (m + 1) F (σ ^ k) := by
  induction k with
  | zero => simp [twistNorm_zero]
  | succ k ih =>
    rw [pow_succ', ih, twistNorm_succ, map_mul,
      ← (standard_automorphism_transport (K := F) (n := m + 1)).2.2.1, pow_succ', map_mul]
    group

theorem twistNorm_succ' (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) (k : ℕ) :
    twistNorm A σ (k + 1) =
      twistNorm A σ k * GeneralLinearGroup.map ((σ ^ k : F ≃+* F) : F →+* F) A := by
  induction k with
  | zero => rw [twistNorm_succ, twistNorm_zero, map_one, mul_one, one_mul, pow_zero,
      map_one_ringAut]
  | succ k ih =>
    calc twistNorm A σ (k + 1 + 1)
        = A * GeneralLinearGroup.map (σ : F →+* F) (twistNorm A σ (k + 1)) :=
          twistNorm_succ A σ (k + 1)
      _ = A * GeneralLinearGroup.map (σ : F →+* F) (twistNorm A σ k) *
            GeneralLinearGroup.map ((σ ^ (k + 1) : F ≃+* F) : F →+* F) A := by
          rw [ih, map_mul, map_map_ringAut, ← pow_succ', mul_assoc]
      _ = twistNorm A σ (k + 1) * GeneralLinearGroup.map ((σ ^ (k + 1) : F ≃+* F) : F →+* F) A := by
          rw [twistNorm_succ]

theorem isPermOf_twistNorm {A : GL (Fin (m + 1)) F} {π : Equiv.Perm (Fin (m + 1))}
    (hA : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) (σ : F ≃+* F) (k : ℕ) :
    IsPermOf ((twistNorm A σ k : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      (π ^ k) := by
  induction k with
  | zero =>
    rw [twistNorm_zero, Units.val_one, pow_zero]
    exact isPermOf_one
  | succ k ih =>
    rw [twistNorm_succ, Units.val_mul, pow_succ']
    exact hA.mul (isPermOf_map σ ih)

theorem twistNorm_apply_succ {A : GL (Fin (m + 1)) F} {π : Equiv.Perm (Fin (m + 1))}
    (hA : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) (σ : F ≃+* F) (k : ℕ)
    (i : Fin (m + 1)) :
    ((twistNorm A σ (k + 1) : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        (π ((π ^ k) i)) i =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (π ((π ^ k) i)) ((π ^ k) i) *
        σ (((twistNorm A σ k : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) ((π ^ k) i) i) := by
  rw [twistNorm_succ, Units.val_mul,
    mul_apply_of_isPermOf (isPermOf_map σ (isPermOf_twistNorm hA σ k)) i,
    GeneralLinearGroup.map_apply]
  rfl

theorem exists_twistNorm_apply_eq {A : GL (Fin (m + 1)) F} {π : Equiv.Perm (Fin (m + 1))}
    (hA : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) {σ : F ≃+* F} {p : ℕ}
    (hσ : ∀ x : Fˣ, ∃ c : Fˣ, σ (x : F) = x * c ^ p) (a : Fin (m + 1) → Fˣ)
    (ha : ∀ i, (a i : F) = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (π i) i) (k : ℕ)
    (i : Fin (m + 1)) : ∃ c : Fˣ,
      ((twistNorm A σ k : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        ((π ^ k) i) i = ((∏ j ∈ Finset.range k, a ((π ^ j) i) : Fˣ) : F) * (c : F) ^ p := by
  induction k with
  | zero => exact ⟨1, by simp [twistNorm_zero]⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := hσ (∏ j ∈ Finset.range k, a ((π ^ j) i))
    refine ⟨c' * Units.map (σ : F →* F) c, ?_⟩
    rw [pow_succ', Equiv.Perm.mul_apply, twistNorm_apply_succ hA, hc, map_mul, map_pow, hc',
      Finset.prod_range_succ, ← ha]
    push_cast
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    ring

end LinModel

end CFSG.StandardType
