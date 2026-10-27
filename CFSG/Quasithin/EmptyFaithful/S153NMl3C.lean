module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.Quasithin.S153N

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial

namespace Ml3

theorem exists_conj_map_le_sylow {G : Type*} [Group G] [Finite G] {A : Type*} [Group A]
    {J Γ S : Subgroup G} (hSΓ : IsSylowTwoOf S Γ) (hJΓ : J ≤ Γ)
    (hΓN : Γ ≤ Subgroup.normalizer (J : Set G)) (π : A →* ↥J) (hπ : Function.Surjective π)
    {Q : Subgroup A} (hQ : IsPGroup 2 Q) :
    ∃ t : A, ∀ u ∈ Q, ((π (t⁻¹ * u * t) : ↥J) : G) ∈ S := by
  set f : A →* G := J.subtype.comp π with hf
  set P : Subgroup G := Q.map f with hP
  have hPJ : P ≤ J := by
    rintro _ ⟨u, -, rfl⟩
    exact (π u).2
  have hP2 : IsPGroup 2 P := hQ.of_surjective (f.subgroupMap Q) (f.subgroupMap_surjective Q)
  have hSJ : IsSylowTwoOf (S ⊓ J) J := B6.isSylowTwoOf_inf_normal hSΓ hJΓ hΓN
  obtain ⟨x, hxJ, hPx⟩ := F7.isSylowTwoOf_exists_conj_le hSJ hPJ hP2
  obtain ⟨t, ht⟩ := hπ ⟨x, hxJ⟩
  refine ⟨t, fun u hu => ?_⟩
  have h1 : f u ∈ P := ⟨u, hu, rfl⟩
  have h2 := mem_conjSub.mp (hPx h1)
  have h3 : ((π (t⁻¹ * u * t) : ↥J) : G) = x⁻¹ * f u * x := by
    rw [map_mul, map_mul, map_inv, ht]
    rfl
  rw [h3]
  exact h2.1

variable {K : Type} [Field K]

theorem fixed_of_unitriangular (v : Fin 3 → K)
    (h : ∀ u ∈ LinearFlag.unitriangular 3 K,
      ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  let u01 : Matrix.SpecialLinearGroup (Fin 3) K :=
    ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  let u12 : Matrix.SpecialLinearGroup (Fin 3) K :=
    ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  have h01 : u01 ∈ LinearFlag.unitriangular 3 K := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [u01] at hji ⊢
    · fin_cases i <;> simp [u01]
  have h12 : u12 ∈ LinearFlag.unitriangular 3 K := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [u12] at hji ⊢
    · fin_cases i <;> simp [u12]
  have e01 := congrFun (h u01 h01) 0
  have e12 := congrFun (h u12 h12) 1
  simp [u01, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e01
  simp [u12, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e12
  exact ⟨e01, e12⟩

theorem corr_mem_of_fix {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {I : Fin 2 → Subgroup W}
    (hind : ∀ i, I i ⊓ (fixV J ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = fixV J)
    (hIinv : ∀ i, ∀ γ ∈ J, ∀ u ∈ I i, γ u ∈ I i) {γ : MulAut W} (hγ : γ ∈ J) {z a₀ a₁ : W}
    (hz : z ∈ fixV J) (ha₀ : a₀ ∈ I 0) (ha₁ : a₁ ∈ I 1) (hfix : γ (z * (a₀ * a₁)) = z * (a₀ * a₁)) :
    γ a₀ * a₀⁻¹ ∈ fixV J ∧ γ a₁ * a₁⁻¹ ∈ fixV J := by
  have hc₀ : γ a₀ * a₀⁻¹ ∈ I 0 := (I 0).mul_mem (hIinv 0 γ hγ a₀ ha₀) ((I 0).inv_mem ha₀)
  have hc₁ : γ a₁ * a₁⁻¹ ∈ I 1 := (I 1).mul_mem (hIinv 1 γ hγ a₁ ha₁) ((I 1).inv_mem ha₁)
  have hprod : (γ a₀ * a₀⁻¹) * (γ a₁ * a₁⁻¹) = 1 := by
    rw [map_mul, map_mul, mem_fixV.mp hz γ hγ] at hfix
    have h' : γ a₀ * γ a₁ = a₀ * a₁ := mul_left_cancel hfix
    calc (γ a₀ * a₀⁻¹) * (γ a₁ * a₁⁻¹) = (γ a₀ * γ a₁) * (a₀⁻¹ * a₁⁻¹) := by
          rw [mul_mul_mul_comm]
      _ = 1 := by rw [h', ← mul_inv, mul_inv_cancel]
  have h01 : γ a₀ * a₀⁻¹ = (γ a₁ * a₁⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have h10 : γ a₁ * a₁⁻¹ = (γ a₀ * a₀⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hm₀ : γ a₀ * a₀⁻¹ ∈ I 1 := by rw [h01]; exact (I 1).inv_mem hc₁
  have hm₁ : γ a₁ * a₁⁻¹ ∈ I 0 := by rw [h10]; exact (I 0).inv_mem hc₀
  refine ⟨?_, ?_⟩
  · rw [← hind 0]
    exact ⟨hc₀, Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
      (Subgroup.mem_iSup_of_mem (by decide) hm₀))⟩
  · rw [← hind 1]
    exact ⟨hc₁, Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 0
      (Subgroup.mem_iSup_of_mem (by decide) hm₁))⟩

end Ml3

end CFSG.Quasithin.S153N
