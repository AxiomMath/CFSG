module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

@[expose] noncomputable def statedOmegaOrthEquiv (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ ≃* orthDerived Q :=
  ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

theorem coe_statedOmegaOrthEquiv (hQ : ⇑Q = Q₀) (A : StatedOmega Q₀) :
    (statedOmegaOrthEquiv hQ A : (ι → K) ≃ₗ[K] (ι → K)) = toLinEquiv ι K A :=
  rfl

@[expose] noncomputable def statedProjOrthEquiv (hQ : ⇑Q = Q₀) :
    StatedProj (StatedOmega Q₀) ≃* ProjOrthDerived Q :=
  QuotientGroup.congr _ _ (statedOmegaOrthEquiv hQ) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
      rw [Subgroup.mem_subgroupOf]
      change ((statedOmegaOrthEquiv hQ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈
        scalars K (ι → K)
      rw [coe_statedOmegaOrthEquiv]
      exact hy
    · intro hx
      refine ⟨(statedOmegaOrthEquiv hQ).symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
      rw [Subgroup.mem_subgroupOf] at hx
      have h1 : (statedOmegaOrthEquiv hQ ((statedOmegaOrthEquiv hQ).symm x) :
          (ι → K) ≃ₗ[K] (ι → K)) = x := by rw [MulEquiv.apply_symm_apply]
      rw [coe_statedOmegaOrthEquiv] at h1
      rw [h1]
      exact hx)

end Bridge

theorem lieCentralizerComponentT_POmegaPlus : LieCentralizerComponentT .POmegaPlus := by
  intro T _ _ p n f hp hp5 hf hmodel x y hxp hx1 hy2 hy1 hxy
  obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ :=
    statedClassicalModel_of_lieModel_classical (by decide) hmodel
  have : CharP K 2 := charP_two_of_card_eq_pow hcard
  have hq : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  set ψ := e.trans (statedProjOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n)
    (K := K))) with hψ
  refine exists_centralizer_component_of_mulEquiv ψ ?_
  refine orth_centralizer_component
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K) hq hp hp5
    (a := ψ x) (b := ψ y) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hxp, map_one]
  · intro h1
    exact hx1 (ψ.injective (by rw [h1, map_one]))
  · rw [← map_pow, hy2, map_one]
  · intro h1
    exact hy1 (ψ.injective (by rw [h1, map_one]))
  · rw [← map_mul, ← map_mul, hxy]

theorem lieCentralizerComponentT_POmegaMinus : LieCentralizerComponentT .POmegaMinus := by
  intro T _ _ p n f hp hp5 hf hmodel x y hxp hx1 hy2 hy1 hxy
  obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    statedClassicalModel_of_lieModel_classical (by decide) hmodel
  have : CharP K 2 := charP_two_of_card_eq_pow hcard
  have hq : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  set ψ := e.trans (statedProjOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadMinus (n := n)
    (K := K) b c)) with hψ
  refine exists_centralizer_component_of_mulEquiv ψ ?_
  refine orth_centralizer_component
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr) hq hp hp5
    (a := ψ x) (b := ψ y) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hxp, map_one]
  · intro h1
    exact hx1 (ψ.injective (by rw [h1, map_one]))
  · rw [← map_pow, hy2, map_one]
  · intro h1
    exact hy1 (ψ.injective (by rw [h1, map_one]))
  · rw [← map_mul, ← map_mul, hxy]

end CFSG.RankThree.PartOne
