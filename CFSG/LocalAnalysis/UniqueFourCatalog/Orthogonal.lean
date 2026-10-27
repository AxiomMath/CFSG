module

public import CFSG.LocalAnalysis.UniqueFourCatalog.ClosureTop
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOrthModel
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcBasic

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits CFSG.LocalAnalysis.RankThreeUC
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

section Orthogonal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem closureTop_of_orthogonal {G : Type} [Group G] (Q : QuadraticForm K (ι → K))
    (Φ : QuadForm K (ι → K)) (hΦ : ⇑Q = Φ.Q)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 3 ≤ Module.finrank K (ι → K))
    (β₀ : LinearMap.BilinForm K (ι → K)) (hβ₀ : ∀ x, β₀ x x = Q x)
    (e : G ≃* StatedProj (StatedOmega Φ.Q)) : ClosureTop G :=
  closureTop_of_proj (StatedOmega Φ.Q) e (fun E P hE' hP hP2 hEN =>
    twoLocalClosure_eq_top_statedOmega Q Φ hΦ hE hnd hd β₀ hβ₀ E P hE' hP hP2 hEN)

end Orthogonal

theorem closureTop_of_POmegaPlus {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    ClosureTop G := by
  refine closureTop_of_orthogonal (quadPlus n K) (quadPlusForm n K) (coe_quadPlus n K)
    (commutator_orthogonalGroup_quadPlus (by omega)) (nondegenerate_polarBilin_quadPlus n K) ?_
    (SpClosure.spB₀ n K) (fun x => ?_) e
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [quadPlus_apply, SpClosure.spB₀, Matrix.toBilin'_apply', SpClosure.dotProduct_spU_mulVec]
    rfl

theorem closureTop_of_POmegaMinus {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) : ClosureTop G := by
  refine closureTop_of_orthogonal (quadMinus n K b c) (quadMinusForm n K b c hirr)
    (coe_quadMinus n K b c) (commutator_orthogonalGroup_quadMinus hn hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) ?_ (orthB₀Minus n K b c)
    (fun x => ?_) e
  · rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [quadMinus_apply]
    simp only [orthB₀Minus, LinearMap.mk₂_apply, sq]
    ring

theorem not_uniqueFour_of_statedPOmegaPlus {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    {n f : ℕ} (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaPlus n 2 f) :
    ¬ uniqueFourUnique G := by
  obtain ⟨⟨-, -, hn⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card hcard
  exact not_uniqueFour_of_closureTop hS (closureTop_of_POmegaPlus hn e)

theorem not_uniqueFour_of_statedPOmegaMinus {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    {n f : ℕ} (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaMinus n 2 f) :
    ¬ uniqueFourUnique G := by
  obtain ⟨⟨-, -, hn⟩, K, hK, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card hcard
  exact not_uniqueFour_of_closureTop hS (closureTop_of_POmegaMinus hn hirr e)

end CFSG.LocalAnalysis.UniqueFourCatalog
