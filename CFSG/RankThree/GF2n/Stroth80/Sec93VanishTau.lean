module

public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFive

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

theorem rho'_apply {K : Type} [Field K]
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    rho' K z X = (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
      ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have h1 : rho' K z X = (specialRho z).val X := rfl
  rw [h1, specialRho_apply]

theorem specialLinearGroup_transpose_one {K : Type} [Field K] :
    (1 : Matrix.SpecialLinearGroup (Fin 2) K).transpose = 1 :=
  Subtype.ext (by simp)

theorem specialLinearGroup_transpose_transpose {K : Type} [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) : A.transpose.transpose = A :=
  Subtype.ext (Matrix.transpose_transpose _)

theorem tau_conj_rho' {K : Type} [Field K] (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    (tau (K := K)).val * rho' K (A, B) * ((tau (K := K)).val)⁻¹ =
      rho' K ((B⁻¹).transpose, (A.transpose)⁻¹) := by
  have hinv : ((tau (K := K)).val)⁻¹ = (tau (K := K)).val :=
    inv_eq_of_mul_eq_one_right (by rw [← Subgroup.coe_mul, tau_mul_tau, Subgroup.coe_one])
  rw [hinv]
  apply LinearEquiv.ext
  intro X
  simp only [LinearEquiv.mul_apply, tau_apply, rho'_apply, inv_inv,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

theorem tau_invariant_normal_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K)
    (N : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
    (hNJ : N ≤ (rho' K).range)
    (hnorm : ∀ g ∈ (rho' K).range, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (htau : ∀ n ∈ N, (tau (K := K)).val * n * ((tau (K := K)).val)⁻¹ ∈ N) :
    N = ⊥ ∨ N = (rho' K).range := by
  classical
  have hNn : (N.comap (rho' K)).Normal := ⟨fun n hn g => by
    have h := hnorm (rho' K g) ⟨g, rfl⟩ (rho' K n) hn
    simpa [← map_mul, ← map_inv] using h⟩
  have hmap : (N.comap (rho' K)).map (rho' K) = N := Subgroup.map_comap_eq_self hNJ
  let A₀ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hA₀ : A₀ ≠ 1 := by
    intro h
    have := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [A₀] at this
  have hA₀t : (A₀.transpose)⁻¹ ≠ 1 := by
    intro h
    apply hA₀
    have h1 : A₀.transpose = 1 := inv_eq_one.mp h
    have h2 := congrArg Matrix.SpecialLinearGroup.transpose h1
    rwa [specialLinearGroup_transpose_transpose, specialLinearGroup_transpose_one] at h2
  have hA₀i : (A₀⁻¹).transpose ≠ 1 := by
    intro h
    apply hA₀
    have h2 := congrArg Matrix.SpecialLinearGroup.transpose h
    rw [specialLinearGroup_transpose_transpose, specialLinearGroup_transpose_one] at h2
    exact inv_eq_one.mp h2
  rcases CFSG.LocalAnalysis.EvenBN.Common.normal_sl2_prod_eq h4 hNn with h | h | h | h
  · left
    rw [← hmap, h, Subgroup.map_bot]
  · exfalso
    have h1 : ((A₀, (1 : Matrix.SpecialLinearGroup (Fin 2) K)) :
        Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) ∈
        N.comap (rho' K) := by
      rw [h]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
    rw [Subgroup.mem_comap] at h1
    have h2' : (tau (K := K)).val * rho' K (A₀, 1) * ((tau (K := K)).val)⁻¹ ∈ N := htau _ h1
    rw [tau_conj_rho', inv_one, specialLinearGroup_transpose_one] at h2'
    have h3 : (((1 : Matrix.SpecialLinearGroup (Fin 2) K), (A₀.transpose)⁻¹) :
        Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) ∈
        N.comap (rho' K) := h2'
    rw [h] at h3
    exact hA₀t (Subgroup.mem_bot.mp (Subgroup.mem_prod.mp h3).2)
  · exfalso
    have h1 : (((1 : Matrix.SpecialLinearGroup (Fin 2) K), A₀) :
        Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) ∈
        N.comap (rho' K) := by
      rw [h]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩
    rw [Subgroup.mem_comap] at h1
    have h2' : (tau (K := K)).val * rho' K (1, A₀) * ((tau (K := K)).val)⁻¹ ∈ N := htau _ h1
    rw [tau_conj_rho', specialLinearGroup_transpose_one, inv_one] at h2'
    have h3 : (((A₀⁻¹).transpose, (1 : Matrix.SpecialLinearGroup (Fin 2) K)) :
        Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) ∈
        N.comap (rho' K) := h2'
    rw [h] at h3
    exact hA₀i (Subgroup.mem_bot.mp (Subgroup.mem_prod.mp h3).1)
  · right
    rw [← hmap, h, Subgroup.map_top]

end CFSG.RankThree.GF2n.Stroth80
