module

public import CFSG.Quasithin.Vol2.Ch11SecAKA14

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spLevi_mem_perfectCore)
open CFSG.Open (pCoreOf)

namespace KA

variable {K : Type} [Field K]

theorem spB_e1 (y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) (vec4 0 1 0 0) y = y (.inr 1) := by
  rw [toBilin'_spJ_apply]
  simp [vec4, Fin.sum_univ_two]

variable [Finite K] [CharP K 2]

theorem shape_of_levi1 (hK4 : ∃ s : Finset K, s.card = 4)
    {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)} {σ : K →+* K}
    (hσ : ∀ (c : K) (x : Fin 2 ⊕ Fin 2 → K), T (c • x) = σ c • T x)
    (hL : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x)
    (hinj : Function.Injective T) (hplane : ∀ x ∈ spPlane K, T x ∈ spPlane K)
    (hlevi : ∀ M ∈ perfectCore (Q2 K 1), ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 1)), ∀ v,
      T (mat 2 K M *ᵥ v) = mat 2 K N *ᵥ (mat 2 K M *ᵥ T v)) :
    (∀ c, σ c = c) ∧ ∃ μ ν : K, μ ≠ 0 ∧ T (vec4 1 0 0 0) = μ • vec4 1 0 0 0 ∧
      T (vec4 0 1 0 0) = μ • vec4 0 1 0 0 ∧ T (vec4 0 0 1 0) (.inr 0) = ν ∧
      T (vec4 0 0 1 0) (.inr 1) = 0 ∧ T (vec4 0 0 0 1) (.inr 0) = 0 ∧
      T (vec4 0 0 0 1) (.inr 1) = ν := by
  have he0P : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ∈ spPlane K := ⟨rfl, rfl⟩
  have he1P : (vec4 0 1 0 0 : Fin 2 ⊕ Fin 2 → K) ∈ spPlane K := ⟨rfl, rfl⟩
  have key : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ spPlane K,
      T (mat 2 K (spLevi 1 A) *ᵥ v) = mat 2 K (spLevi 1 A) *ᵥ T v := by
    intro A v hv
    obtain ⟨N, hN, hTN⟩ := hlevi _ (spLevi_mem_perfectCore hK4 1 A)
    rw [hTN, pCore1_mulVec hK4 hN]
    rw [spLevi1_mulVec_plane A (hplane v hv)]
    exact ⟨rfl, rfl⟩
  obtain ⟨a2, a3⟩ := hplane _ he0P
  obtain ⟨b2, b3⟩ := hplane _ he1P
  let up : K → Matrix.SpecialLinearGroup (Fin 2) K := fun t =>
    ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let lo : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hup0 : ∀ t, mat 2 K (spLevi 1 (up t)) *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0 := fun t => by
    rw [spLevi1_mulVec_plane (up t) he0P]
    exact vec4_eq (by simp [vec4, up]) (by simp [vec4, up]) rfl rfl
  have hup1 : ∀ t, mat 2 K (spLevi 1 (up t)) *ᵥ vec4 0 1 0 0 =
      t • vec4 1 0 0 0 + vec4 0 1 0 0 := fun t => by
    rw [spLevi1_mulVec_plane (up t) he1P]
    exact vec4_eq (by simp [vec4, up]) (by simp [vec4, up]) (by simp [vec4]) (by simp [vec4])
  have hlo1 : mat 2 K (spLevi 1 lo) *ᵥ vec4 0 1 0 0 = vec4 0 1 0 0 := by
    rw [spLevi1_mulVec_plane lo he1P]
    exact vec4_eq (by simp [vec4, lo]) (by simp [vec4, lo]) rfl rfl
  have k1 := key (up 1) _ he0P
  rw [hup0, spLevi1_mulVec_plane (up 1) (hplane _ he0P)] at k1
  have a1 : T (vec4 1 0 0 0) (.inl 1) = 0 := by
    have := congrFun k1 (.inl 0)
    simpa [vec4, up] using this
  have k2 := key lo _ he1P
  rw [hlo1, spLevi1_mulVec_plane lo (hplane _ he1P)] at k2
  have b0 : T (vec4 0 1 0 0) (.inl 0) = 0 := by
    have := congrFun k2 (.inl 1)
    simpa [vec4, lo] using this
  have k3 : ∀ t : K, σ t * T (vec4 1 0 0 0) (.inl 0) = t * T (vec4 0 1 0 0) (.inl 1) := by
    intro t
    have := key (up t) _ he1P
    rw [hup1, map_add, hσ, spLevi1_mulVec_plane (up t) (hplane _ he1P)] at this
    have h := congrFun this (.inl 0)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl0, b0, mul_zero,
      add_zero, zero_add] at h
    simpa [up] using h
  obtain ⟨μ, hμ⟩ : ∃ μ, T (vec4 1 0 0 0) (.inl 0) = μ := ⟨_, rfl⟩
  have hb1 : T (vec4 0 1 0 0) (.inl 1) = μ := by
    have := k3 1
    rw [map_one, one_mul, one_mul, hμ] at this
    exact this.symm
  have he0 : T (vec4 1 0 0 0) = μ • vec4 1 0 0 0 :=
    vec4_eq (by rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one, hμ])
      (by rw [Pi.smul_apply, vec4_apply_inl1, smul_eq_mul, mul_zero, a1])
      (by rw [Pi.smul_apply, vec4_apply_inr0, smul_eq_mul, mul_zero, a2])
      (by rw [Pi.smul_apply, vec4_apply_inr1, smul_eq_mul, mul_zero, a3])
  have he1 : T (vec4 0 1 0 0) = μ • vec4 0 1 0 0 :=
    vec4_eq (by rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_zero, b0])
      (by rw [Pi.smul_apply, vec4_apply_inl1, smul_eq_mul, mul_one, hb1])
      (by rw [Pi.smul_apply, vec4_apply_inr0, smul_eq_mul, mul_zero, b2])
      (by rw [Pi.smul_apply, vec4_apply_inr1, smul_eq_mul, mul_zero, b3])
  have hμ0 : μ ≠ 0 := by
    intro h
    have h1 : T (vec4 1 0 0 0) = T 0 := by rw [he0, h, zero_smul, map_zero]
    simpa [vec4] using congrFun (hinj h1) (.inl 0)
  have hσ1 : ∀ c, σ c = c := fun c => by
    have := k3 c
    rw [hμ, hb1] at this
    exact mul_right_cancel₀ hμ0 this
  have hlin : ∀ (c : K) x, T (c • x) = c • T x := fun c x => by rw [hσ, hσ1]
  let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := T, map_add' := map_add T, map_smul' := fun c v => hlin c v }
  obtain ⟨m, hm⟩ := exists_similitude TL fun γ => by
    obtain ⟨γ', hγ'⟩ := hL γ
    exact ⟨γ', fun x => hγ' x⟩
  have hB : ∀ x y, Matrix.toBilin' (spJ K) (T x) (T y) = m * Matrix.toBilin' (spJ K) x y :=
    hm
  have e00 := hB (vec4 1 0 0 0) (vec4 0 0 1 0)
  have e10 := hB (vec4 0 1 0 0) (vec4 0 0 1 0)
  have e01 := hB (vec4 1 0 0 0) (vec4 0 0 0 1)
  have e11 := hB (vec4 0 1 0 0) (vec4 0 0 0 1)
  rw [he0, LinearMap.map_smul₂, spB_e0, spB_e0, smul_eq_mul] at e00 e01
  rw [he1, LinearMap.map_smul₂, spB_e1, spB_e1, smul_eq_mul] at e10 e11
  simp only [vec4_apply_inr0, vec4_apply_inr1, mul_one, mul_zero] at e00 e01 e10 e11
  refine ⟨hσ1, μ, m / μ, hμ0, he0, he1, ?_, ?_, ?_, ?_⟩
  · rw [eq_div_iff hμ0, mul_comm]
    exact e00
  · exact (mul_eq_zero.mp e10).resolve_left hμ0
  · exact (mul_eq_zero.mp e01).resolve_left hμ0
  · rw [eq_div_iff hμ0, mul_comm]
    exact e11

end KA

end CFSG.Quasithin.Vol2.KGNat
