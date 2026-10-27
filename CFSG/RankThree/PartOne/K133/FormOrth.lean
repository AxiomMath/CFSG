module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG.LieType.BorelTits Module Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem ReflForm.β_sum_left (F : ReflForm K V) {ι : Type*} (s : Finset ι) (f : ι → V) (v : V) :
    F.β (∑ i ∈ s, f i) v = ∑ i ∈ s, F.β (f i) v :=
  map_sum (AddMonoidHom.mk' (fun u => F.β u v) (fun u u' => F.add_left u u' v)) f s

theorem ReflForm.β_sum_right (F : ReflForm K V) {ι : Type*} (s : Finset ι) (u : V) (f : ι → V) :
    F.β u (∑ i ∈ s, f i) = ∑ i ∈ s, F.β u (f i) :=
  map_sum (AddMonoidHom.mk' (fun v => F.β u v) (fun v v' => F.add_right u v v')) f s

theorem β_eq_zero_of_eigen (F : ReflForm K V) {g : V → V} (hg : ∀ x y, F.β (g x) (g y) = F.β x y)
    {x y : V} {a c : K} (hx : g x = a • x) (hy : g y = c • y) (h : F.σ a * c ≠ 1) : F.β x y = 0 := by
  have h1 := hg x y
  rw [hx, hy, F.smul_left, F.smul_right] at h1
  by_contra hne
  apply h
  have : (F.σ a * c) * F.β x y = 1 * F.β x y := by linear_combination h1
  exact mul_right_cancel₀ hne this

theorem isometry_of_basis (F : ReflForm K V) {ι : Type*} [Fintype ι] (b : Basis ι K V) (τ : V →ₗ[K] V)
    (h : ∀ j k, F.β (τ (b j)) (τ (b k)) = F.β (b j) (b k)) (x y : V) :
    F.β (τ x) (τ y) = F.β x y := by
  classical
  have key : ∀ x y : V, F.β x y =
      ∑ j, ∑ k, F.σ (b.repr x j) * (b.repr y k * F.β (b j) (b k)) := by
    intro x y
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    rw [ReflForm.β_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ReflForm.β_sum_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [F.smul_left, F.smul_right]
  have key' : F.β (τ x) (τ y) =
      ∑ j, ∑ k, F.σ (b.repr x j) * (b.repr y k * F.β (τ (b j)) (τ (b k))) := by
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    rw [map_sum, map_sum, ReflForm.β_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ReflForm.β_sum_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, F.smul_left, F.smul_right]
  rw [key', key x y]
  simp only [h]

theorem exists_sign_matrix_four (F : ReflForm K (Fin 4 → K)) (b : Basis (Fin 4) K (Fin 4 → K))
    (hb : ∀ j k, j ≠ k → F.β (b j) (b k) = 0) :
    ∃ M : Matrix (Fin 4) (Fin 4) K, M.det = 1 ∧ (∀ x y, F.β (M *ᵥ x) (M *ᵥ y) = F.β x y) ∧
      (∀ j, M *ᵥ b j = (if (j : ℕ) < 2 then (-1 : K) else 1) • b j) := by
  classical
  let ε : Fin 4 → K := fun j => if (j : ℕ) < 2 then (-1 : K) else 1
  let τ : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := b.constr K (fun j => ε j • b j)
  have hτ : ∀ j, τ (b j) = ε j • b j := fun j => by simp [τ]
  have hM : ∀ x, (LinearMap.toMatrix' τ) *ᵥ x = τ x := fun x => LinearMap.toMatrix'_mulVec τ x
  have hεσ : ∀ j, F.σ (ε j) * ε j = 1 := by
    intro j
    simp only [ε]
    split_ifs <;> simp
  refine ⟨LinearMap.toMatrix' τ, ?_, ?_, ?_⟩
  · have h1 : (LinearMap.toMatrix' τ).det = LinearMap.det τ := LinearMap.det_toMatrix' τ
    have h2 : (LinearMap.toMatrix b b τ).det = LinearMap.det τ := LinearMap.det_toMatrix b τ
    have h3 : LinearMap.toMatrix b b τ = Matrix.diagonal ε := by
      ext i j
      rw [LinearMap.toMatrix_apply, hτ, map_smul, Basis.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [h1, ← h2, h3, Matrix.det_diagonal, Fin.prod_univ_four]
    simp [ε]
  · intro x y
    rw [hM, hM]
    refine isometry_of_basis F b τ (fun j k => ?_) x y
    rw [hτ, hτ, F.smul_left, F.smul_right]
    by_cases hjk : j = k
    · subst hjk
      calc F.σ (ε j) * (ε j * F.β (b j) (b j)) = (F.σ (ε j) * ε j) * F.β (b j) (b j) := by ring
        _ = F.β (b j) (b j) := by rw [hεσ, one_mul]
    · simp [hb j k hjk]
  · intro j
    rw [hM, hτ]

end CFSG.RankThree.PartOne.K133
