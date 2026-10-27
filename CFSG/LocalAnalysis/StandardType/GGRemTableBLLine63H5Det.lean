module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import Mathlib

public section

namespace CFSG.StandardType.Line63.H5

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Det

variable {K : Type*} [Field K]

theorem irreducible_X_pow_three_sub_C_of_not_cube {c : K} (hc : ∀ d : K, d ^ 3 ≠ c) :
    Irreducible (X ^ 3 - C c : K[X]) := by
  have hdeg : (X ^ 3 - C c : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp)
    fun μ hμ => ?_
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hμ
  exact hc μ hμ

theorem det_eq_sq_of_pow_three_eq_smul {c : K} (hc : ∀ d : K, d ^ 3 ≠ c)
    {M : Matrix (Fin 6) (Fin 6) K} (hM : M ^ 3 = c • (1 : Matrix (Fin 6) (Fin 6) K)) :
    M.det = c ^ 2 := by
  classical
  set a : K[X] := X ^ 3 - C c with ha
  haveI : Fact (Irreducible a) := ⟨irreducible_X_pow_three_sub_C_of_not_cube hc⟩
  set x : Module.End K (Fin 6 → K) := Matrix.toLin' M with hx
  have hax : aeval x a = 0 := by
    rw [ha, map_sub, map_pow, aeval_X, aeval_C, hx, ← Matrix.toLin'_pow, hM]
    ext v i
    simp [Matrix.toLin'_apply, Module.algebraMap_end_apply, Matrix.smul_mulVec]
  have htop : primaryComponent x a = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, hax]
    rfl
  have hdeg : a.natDegree = 3 := natDegree_X_pow_sub_C
  have hfin : Module.finrank K (primaryComponent x a) = 6 := by
    rw [htop, finrank_top]
    simp
  have hm : Module.finrank (AdjoinRoot a) (primaryComponent x a) = 2 := by
    have h := finrank_primaryComponent x a
    rw [hfin, hdeg] at h
    omega
  set γ : Module.End (AdjoinRoot a) (primaryComponent x a) :=
    (AdjoinRoot.root a) • LinearMap.id with hγ
  have hγr : γ.restrictScalars K = primaryRestrict x a := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [hγ, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply,
      coe_primaryRestrict]
    exact coe_root_smul_primaryComponent x a v
  have hdet1 : LinearMap.det (primaryRestrict x a) = Algebra.norm K (LinearMap.det γ) := by
    rw [← hγr]
    exact LinearMap.det_restrictScalars
  have hdet2 : LinearMap.det γ = (AdjoinRoot.root a) ^ 2 := by
    rw [hγ, LinearMap.det_smul, LinearMap.det_id, mul_one, hm]
  have hnorm : Algebra.norm K (AdjoinRoot.root a) = c := by
    have hf : a ≠ 0 := (Fact.out : Irreducible a).ne_zero
    have hmon : a.Monic := monic_X_pow_sub_C _ (by norm_num)
    rw [← AdjoinRoot.powerBasis_gen hf, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
      AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon, AdjoinRoot.powerBasis_dim, hdeg, ha]
    simp
    ring
  have hdet3 : LinearMap.det x = LinearMap.det (primaryRestrict x a) := by
    set e : primaryComponent x a ≃ₗ[K] (Fin 6 → K) := LinearEquiv.ofTop _ htop with he
    rw [← LinearMap.det_conj (primaryRestrict x a) e]
    congr 1
  rw [← LinearMap.det_toLin' M, ← hx, hdet3, hdet1, hdet2, map_pow, hnorm]

theorem det_smul_ne_one_of_pow_three_eq_smul {c : K} (hc : ∀ d : K, d ^ 3 ≠ c)
    {M : Matrix (Fin 6) (Fin 6) K} (hM : M ^ 3 = c • (1 : Matrix (Fin 6) (Fin 6) K)) (t : K) :
    (t • M).det ≠ 1 := by
  intro h1
  rw [Matrix.det_smul, det_eq_sq_of_pow_three_eq_smul hc hM, Fintype.card_fin] at h1
  have h3 : (c * t ^ 2) ^ 3 = c := by
    calc (c * t ^ 2) ^ 3 = c * (t ^ 6 * c ^ 2) := by ring
      _ = c := by rw [h1, mul_one]
  exact hc _ h3

end Det

end CFSG.StandardType.Line63.H5

end
