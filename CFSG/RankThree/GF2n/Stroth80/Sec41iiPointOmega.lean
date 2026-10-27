module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorNat
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

private theorem card_le_root_of_singular {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h4 : 4 ≤ Fintype.card ι)
    {u : ι → K} (hu : u ≠ 0) (hQu : Q u = 0) (X : Subgroup (GL ι K))
    (e : ↥X ≃* CFSG.ClassicalGroups.Orthogonal.Gom Q)
    (he : ∀ (A : ↥X) (v : ι → K), (e A).app v = (A : GL ι K).val *ᵥ v)
    (P : Subgroup (GL ι K)) (hP : P ≤ X) (hP2 : ∀ p ∈ P, p * p = 1)
    (hPfix : ∀ p ∈ P, (p : Matrix ι ι K) *ᵥ u = u)
    (hPnorm : ∀ g ∈ X, (∃ c : K, (g : Matrix ι ι K) *ᵥ u = c • u) → ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    Nat.card P ≤ Nat.card K ^ (Fintype.card ι - 2) := by
  have hdim : Module.finrank K (ι → K) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card K
  haveI : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (DFunLike.coe : ((ι → K) ≃ₗ[K] (ι → K)) → ((ι → K) → (ι → K)))
      LinearEquiv.coe_injective
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (CFSG.ClassicalGroups.Orthogonal.Gom Q),
      N = (P.subgroupOf X).map e.toMonoidHom := ⟨_, rfl⟩
  have hcardN : Nat.card N = Nat.card P := by
    rw [hN]
    exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv)
  have hNle : N ≤ CFSG.ClassicalGroups.Orthogonal.pointStabilizer Q u := by
    rw [hN]
    rintro _ ⟨s, hs, rfl⟩
    refine CFSG.ClassicalGroups.Orthogonal.mem_pointStabilizer.mpr ⟨1, ?_⟩
    rw [one_smul]
    exact (he s u).trans (hPfix _ (Subgroup.mem_subgroupOf.mp hs))
  have hNsq : ∀ y ∈ N, y * y = 1 := by
    rw [hN]
    rintro _ ⟨s, hs, rfl⟩
    have hss : s * s = 1 := Subtype.ext (hP2 _ (Subgroup.mem_subgroupOf.mp hs))
    rw [← map_mul e.toMonoidHom, hss, map_one]
  have hNp : IsPGroup 2 N := by
    intro y
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hNsq y.1 y.2)⟩
  have hNnorm : ∀ x ∈ CFSG.ClassicalGroups.Orthogonal.pointStabilizer Q u, ∀ y ∈ N,
      x * y * x⁻¹ ∈ N := by
    rw [hN]
    intro x hx y hy
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.mem_pointStabilizer.mp hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨g, rfl⟩ := e.surjective x
    have hcg : ((g : GL ι K) : Matrix ι ι K) *ᵥ u = c • u := (he g u).symm.trans hc
    have hmem := hPnorm (g : GL ι K) g.2 ⟨c, hcg⟩ (s : GL ι K) (Subgroup.mem_subgroupOf.mp hs)
    refine Subgroup.mem_map.mpr ⟨g * s * g⁻¹, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    simp [map_mul, map_inv]
  have hNL : N ≤ CFSG.ClassicalGroups.Orthogonal.Lom Q u := by
    rw [CFSG.ClassicalGroups.Orthogonal.Lom_eq_pCoreOf_pointStabilizer_of_four_le hQ
      (by rw [hdim]; exact h4) hu hQu]
    exact CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hNle hNnorm hNp
  have hLom : Nat.card (CFSG.ClassicalGroups.Orthogonal.Lom Q u) =
      Nat.card K ^ (Fintype.card ι - 2) := by
    have h1 : Nat.card (CFSG.ClassicalGroups.Orthogonal.Lom Q u) =
        Nat.card (CFSG.ClassicalGroups.Orthogonal.rootGroup Q u) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (CFSG.ClassicalGroups.Orthogonal.rootGroup_le_elementaryGroup Q u)).toEquiv
    rw [h1, CFSG.ClassicalGroups.Orthogonal.card_rootGroup hQ hQu hu, hdim]
  calc Nat.card P = Nat.card N := hcardN.symm
    _ ≤ Nat.card (CFSG.ClassicalGroups.Orthogonal.Lom Q u) := Subgroup.card_le_of_le hNL
    _ = Nat.card K ^ (Fintype.card ι - 2) := hLom

theorem classicalPointOmega_of_nonsingular (h : ClassicalPointNonsingularStatement) :
    (∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ m : ℕ, 3 ≤ m → PointBound K
        (StatedOmega (StatedQuadPlus m K))) ∧ (∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card
        K → ∀ (m : ℕ) (b c : K), 2 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) → PointBound K
        (StatedOmega (StatedQuadMinus m K b c))) := by
  refine ⟨?_, ?_⟩
  · intro K _ _ _ hq m hm u hu P hPX hP2 hPfix hPnorm
    have hcard : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
      rw [Fintype.card_sum, Fintype.card_fin]
      omega
    have hKpos : 0 < Nat.card K := by omega
    refine ⟨?_, fun h3 => ?_⟩
    · by_cases hQu : StatedQuadPlus m K u = 0
      · have hQu' : CFSG.LieType.Universal.Spin.quadPlus m K u = 0 :=
          (congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus m K) u).trans hQu
        have hb := card_le_root_of_singular (CFSG.LieType.Universal.Spin.quadPlus m K)
          (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K) (by omega) hu hQu'
          (StatedOmega (StatedQuadPlus m K))
          (CFSG.ClassicalGroups.Orthogonal.statedOmegaPlusEquiv hm)
          (fun A v => CFSG.ClassicalGroups.Orthogonal.statedOmegaPlusEquiv_app hm A v)
          P hPX hP2 hPfix hPnorm
        rw [hcard]
        exact hb.trans (Nat.pow_le_pow_right hKpos (by omega))
      · have hPbot : P = ⊥ := (h K hq).1 m hm u hu hQu P hPX hP2 hPfix hPnorm
        rw [hPbot, Subgroup.card_bot]
        exact Nat.one_le_pow _ _ hKpos
    · rw [hcard] at h3
      exfalso
      omega
  · intro K _ _ _ hq m b c hm hirr u hu P hPX hP2 hPfix hPnorm
    have hcard : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hKpos : 0 < Nat.card K := by omega
    refine ⟨?_, fun h3 => ?_⟩
    · by_cases hQu : StatedQuadMinus m K b c u = 0
      · have hQu' : CFSG.LieType.Universal.Spin.quadMinus m K b c u = 0 :=
          (congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus m K b c) u).trans hQu
        have hb := card_le_root_of_singular (CFSG.LieType.Universal.Spin.quadMinus m K b c)
          (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
          (by omega) hu hQu' (StatedOmega (StatedQuadMinus m K b c))
          (CFSG.ClassicalGroups.Orthogonal.statedOmegaMinusEquiv hm hirr)
          (fun A v => CFSG.ClassicalGroups.Orthogonal.statedOmegaMinusEquiv_app hm hirr A v)
          P hPX hP2 hPfix hPnorm
        rw [hcard]
        exact hb.trans (Nat.pow_le_pow_right hKpos (by omega))
      · have hPbot : P = ⊥ := (h K hq).2 m b c hm hirr u hu hQu P hPX hP2 hPfix hPnorm
        rw [hPbot, Subgroup.card_bot]
        exact Nat.one_le_pow _ _ hKpos
    · rw [hcard] at h3
      exfalso
      omega

end CFSG.RankThree.GF2n.Stroth80
