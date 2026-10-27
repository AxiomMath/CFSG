module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped Matrix

theorem vanishGeom_gom_isometry {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q : QuadraticForm K (ι → K)} (g : Gom Q) (v : ι → K) : Q (Gom.app g v) = Q v :=
  map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2) v

theorem vanishGeom_isometry_of_mem {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X)
    {A : GL ι K} (hA : A ∈ X) (v : ι → K) : Q' ((A : Matrix ι ι K) *ᵥ v) = Q' v := by
  rw [← E.app ⟨A, hA⟩ v]
  exact vanishGeom_gom_isometry _ v

theorem vanishGeom_matrix_eq_of_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {M N : Matrix ι ι K} (h : ∀ w, M *ᵥ w = N *ᵥ w) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem vanishGeom_isometry_of_normalizer {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [CharP K 2] {Q' : QuadraticForm K (ι → K)}
    (hQ : (polarBilin Q').Nondegenerate) {X : Subgroup (GL ι K)}
    (hN : ∀ A : GL ι K, (∀ g ∈ X, A * g * A⁻¹ ∈ X) →
      ∃ c : K, c ≠ 0 ∧ ∀ v, Q' (c • ((A : Matrix ι ι K) *ᵥ v)) = Q' v)
    (F : (ι → K) →ₗ[K] (ι → K)) (hFF : ∀ w, F (F w) = w)
    (hcomp : ∀ g ∈ X, ∃ g' ∈ X, ∀ w, F ((g : Matrix ι ι K) *ᵥ F w) = (g' : Matrix ι ι K) *ᵥ w) :
    ∀ v, Q' (F v) = Q' v := by
  classical
  let MF : Matrix ι ι K := LinearMap.toMatrix' F
  have hMF : MF * MF = 1 := by
    have h1 : LinearMap.toMatrix' (F ∘ₗ F) = LinearMap.toMatrix' LinearMap.id := by
      rw [show F ∘ₗ F = LinearMap.id from LinearMap.ext hFF]
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h1
    exact h1
  have hmul : ∀ w, MF *ᵥ w = F w := fun w => LinearMap.toMatrix'_mulVec F w
  let A : GL ι K := ⟨MF, MF, hMF, hMF⟩
  have hAX : ∀ g ∈ X, A * g * A⁻¹ ∈ X := by
    intro g hg
    obtain ⟨g', hg'X, hg'⟩ := hcomp g hg
    have heq : ((A * g * A⁻¹ : GL ι K) : Matrix ι ι K) = (g' : Matrix ι ι K) := by
      apply vanishGeom_matrix_eq_of_mulVec
      intro w
      show (MF * (g : Matrix ι ι K) * MF) *ᵥ w = (g' : Matrix ι ι K) *ᵥ w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmul, hmul] at *
      exact hg' w
    have : A * g * A⁻¹ = g' := Units.ext heq
    rw [this]
    exact hg'X
  obtain ⟨c, hc0, hc⟩ := hN A hAX
  have hc' : ∀ v, c ^ 2 * Q' (F v) = Q' v := by
    intro v
    have := hc v
    rw [show ((A : GL ι K) : Matrix ι ι K) *ᵥ v = F v from hmul v] at this
    rw [← this, QuadraticMap.map_smul]
    ring
  have hnz : ∃ v, Q' v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hz : (Pi.single i (1 : K) : ι → K) = 0 := hQ.1 _ fun n => by
      have h1 := QuadraticMap.map_add Q' (Pi.single i (1 : K)) n
      have h2 := hcon (Pi.single i (1 : K) + n)
      have h3 := hcon (Pi.single i (1 : K))
      have h4 := hcon n
      simp only [polarBilin_apply_apply]
      rw [h2, h3, h4] at h1
      linear_combination -h1
    have : (Pi.single i (1 : K) : ι → K) ≠ 0 := by
      intro h
      have := congrFun h i
      simp at this
    exact this hz
  have hF2 : ∀ v, Q' (F v) = c ^ 2 * Q' v := by
    intro v
    have h1 := hc' (F v)
    rw [hFF v] at h1
    exact h1.symm
  have hc4 : c ^ 4 = 1 := by
    obtain ⟨v₀, hv₀⟩ := hnz
    have h1 := hc' v₀
    rw [hF2 v₀] at h1
    have h2 : (c ^ 4 - 1) * Q' v₀ = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.mp h2).resolve_right hv₀
    linear_combination h3
  have hc1 : c = 1 := by
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have h5 : (c - 1) ^ 4 = 0 := by
      linear_combination hc4 + (-2 * c ^ 3 + 3 * c ^ 2 - 2 * c + 1) * h2K
    have h6 : c - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h5
    linear_combination h6
  intro v
  rw [hF2 v, hc1, one_pow, one_mul]

end CFSG.RankThree.GF2n.Stroth80
