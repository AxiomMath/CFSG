module

public import CFSG.RankThree.GF2n.Smith81.Orth52Std

public section

namespace CFSG.RankThree.GF2n.Smith81

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem orthTensorLin_apply (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) →ₗ[K] (ι → K))
    (p : (ι → K) × (ι → K)) : orthTensorLin g o p = orthTensor g o p :=
  rfl

theorem transv_sub_one_apply (o : (ι → K) →ₗ[K] (ι → K)) (s : K) (a b : ι → K) :
    (orthTensorLin (!![1, s; 0, 1]) o - 1) (a, b) = (o a + s • o b - a, o b - b) := by
  simp [orthTensorLin_apply, orthTensor]

theorem range_eq_ker_transv (o : (ι → K) →ₗ[K] (ι → K)) (ho : o ∘ₗ o = 1) {s : K} (hs : s ≠ 0) :
    LinearMap.ker (orthTensorLin (!![1, s; 0, 1]) o - 1) =
      LinearMap.range (orthTensorLin (!![1, s; 0, 1]) o - 1) ∧
    Module.finrank K (LinearMap.range (orthTensorLin (!![1, s; 0, 1]) o - 1)) =
      Fintype.card ι := by
  have hoo : ∀ x, o (o x) = x := fun x => by simpa using LinearMap.congr_fun ho x
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h2 : ∀ v : ι → K, (2 : K) • v = 0 := fun v => by rw [h2K, zero_smul]
  have hc : ∀ x : ι → K, x - o x = o x - x := fun x => by
    have h : x - o x - (o x - x) = (2 : K) • (x - o x) := by module
    rw [h2, sub_eq_zero] at h
    exact h
  have hle : LinearMap.range (orthTensorLin (!![1, s; 0, 1]) o - 1) ≤
      LinearMap.ker (orthTensorLin (!![1, s; 0, 1]) o - 1) := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [LinearMap.mem_ker, transv_sub_one_apply, transv_sub_one_apply, Prod.mk_eq_zero]
    constructor
    · simp only [map_add, map_sub, map_smul, hoo]
      linear_combination (norm := module) h2 (a + s • b - o a - s • o b)
    · simp only [map_sub, hoo]
      linear_combination (norm := module) h2 (b - o b)
  have hker : LinearMap.ker (orthTensorLin (!![1, s; 0, 1]) o - 1) =
      LinearMap.range (LinearMap.id.prod (s⁻¹ • (o - 1))) := by
    ext ⟨a, b⟩
    rw [LinearMap.mem_ker, transv_sub_one_apply, Prod.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨h1, h2'⟩
      have hob : o b = b := sub_eq_zero.mp h2'
      rw [hob] at h1
      have hsb : s • b = o a - a := by
        rw [← hc a]
        linear_combination (norm := module) h1
      refine ⟨a, ?_⟩
      simp only [LinearMap.coe_prod, Function.prod_apply, LinearMap.id_apply,
        LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, Prod.mk.injEq, true_and]
      rw [← hsb, smul_smul, inv_mul_cancel₀ hs, one_smul]
    · rintro ⟨x, hx⟩
      simp only [LinearMap.coe_prod, Function.prod_apply, LinearMap.id_apply,
        LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp only [map_smul, map_sub, hoo]
      refine ⟨?_, ?_⟩
      · rw [smul_inv_smul₀ hs]
        abel
      · rw [← hc x, sub_self]
  have hinj : Function.Injective (LinearMap.id.prod (s⁻¹ • (o - 1))) := by
    intro x y hxy
    have := congrArg Prod.fst hxy
    simpa using this
  have hfin : Module.finrank K (LinearMap.ker (orthTensorLin (!![1, s; 0, 1]) o - 1)) =
      Fintype.card ι := by
    rw [hker, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have hrn := LinearMap.finrank_range_add_finrank_ker (orthTensorLin (!![1, s; 0, 1]) o - 1)
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hfin] at hrn
  have hrange : Module.finrank K (LinearMap.range (orthTensorLin (!![1, s; 0, 1]) o - 1)) =
      Fintype.card ι := by
    omega
  exact ⟨(Submodule.eq_of_le_of_finrank_eq hle (by rw [hrange, hfin])).symm, hrange⟩

theorem orthTensorLin_one_sub (o : (ι → K) →ₗ[K] (ι → K)) :
    orthTensorLin 1 o - 1 = LinearMap.prodMap (o - 1) (o - 1) := by
  refine LinearMap.ext fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [LinearMap.sub_apply, Module.End.one_apply, orthTensorLin_apply]
  simp [orthTensor, Matrix.one_apply]

theorem finrank_range_one (o : (ι → K) →ₗ[K] (ι → K)) :
    Module.finrank K (LinearMap.range (orthTensorLin 1 o - 1)) =
      2 * Module.finrank K (LinearMap.range (o - 1)) := by
  rw [orthTensorLin_one_sub, LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq,
    Module.finrank_prod]
  ring

end CFSG.RankThree.GF2n.Smith81
