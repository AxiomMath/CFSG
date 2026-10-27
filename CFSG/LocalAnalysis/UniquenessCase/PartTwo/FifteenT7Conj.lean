module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def s15T7Config (M E U F C K : Subgroup G) : Prop :=
  IsElemAbelian 2 F ∧ F ≤ M ∧ C ≤ F ∧ F ≤ normalizer (E : Set G) ∧
    (∀ x ∈ F, x ∈ C ↔ ∀ d ∈ E, x * d * x⁻¹ * d⁻¹ ∈ U) ∧ U ≤ K ∧ K ≤ E ∧
    E3.mQuot E K = 1 ∧ (∀ x ∈ F, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ U) ∧ 2 ≤ E3.mQuot F C

@[expose] def RT7One (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ F C K : Subgroup G,
        s15T7Config D.M
          (wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L)
          (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) F C K →
          gamma15 D.M V₀ V h.hyp151.isElemAbelian L = 3 ∧
            s15 D.M V₀ V h.hyp151.isElemAbelian L = 2

theorem s15_T7_conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_sup _ _ _

theorem s15_T7_config_conj (M E U F C K : Subgroup G) (g : G)
    (h : s15T7Config (conjSubgroup M g) (conjSubgroup E g) (conjSubgroup U g) F C K) :
    s15T7Config M E U (conjSubgroup F g⁻¹) (conjSubgroup C g⁻¹) (conjSubgroup K g⁻¹) := by
  obtain ⟨hFab, hFM, hCF, hFN, hC, hUK, hKE, hmK, hFK, hmFC⟩ := h
  refine ⟨E3.isElemAbelian_conjSubgroup hFab g⁻¹, ?_, E3.conjSubgroup_mono_left g⁻¹ hCF, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have := E3.conjSubgroup_mono_left g⁻¹ hFM
    rwa [E3.conjSubgroup_conj_inv] at this
  · have := E3.conjSubgroup_mono_left g⁻¹ hFN
    rwa [E3.conjSubgroup_normalizer, E3.conjSubgroup_conj_inv] at this
  · intro x hx
    rw [mem_conjSubgroup_iff, inv_inv] at hx
    have key := hC _ hx
    rw [mem_conjSubgroup_iff, inv_inv, key]
    constructor
    · intro hd d hd'
      have := hd (g⁻¹ * d * g) (by
        rw [mem_conjSubgroup_iff]
        simpa [mul_assoc] using hd')
      rw [mem_conjSubgroup_iff] at this
      simpa [mul_assoc] using this
    · intro hd d hd'
      rw [mem_conjSubgroup_iff] at hd' ⊢
      have := hd (g * d * g⁻¹) hd'
      simpa [mul_assoc] using this
  · have := E3.conjSubgroup_mono_left g⁻¹ hUK
    rwa [E3.conjSubgroup_conj_inv] at this
  · have := E3.conjSubgroup_mono_left g⁻¹ hKE
    rwa [E3.conjSubgroup_conj_inv] at this
  · rw [← E3.mQuot_conjSubgroup (conjSubgroup E g) K g⁻¹, E3.conjSubgroup_conj_inv] at hmK
    exact hmK
  · intro x hx k hk
    rw [mem_conjSubgroup_iff, inv_inv] at hx hk
    have := hFK _ hx _ hk
    rw [mem_conjSubgroup_iff] at this
    simpa [mul_assoc] using this
  · rwa [E3.mQuot_conjSubgroup]

theorem s15_T7_rt7_of_one (D : Data G) (h1 : RT7One D) : RT7 D := by
  intro V₀ V L h hL g X hX F C K hFab hFM hCF hFN hC hUK hKE hmK hFK hmFC
  obtain ⟨m, hm, rfl⟩ := hX
  have hv1 : conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) m =
      v1Sub D.M V₀ V h.hyp151.isElemAbelian L :=
    s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 h.hyp151.isElemAbelian hm
  have hM : conjSubgroup D.M m = D.M :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hm)
  have hE : conjSubgroup (conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) m ⊔
      v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g =
      conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L ⊔
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g) := by
    rw [← conjSubgroup_conjSubgroup, s15_T7_conjSubgroup_sup (wSub V₀ V _ L) _ m, hv1]
  have hU : conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g =
      conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g) := by
    rw [← conjSubgroup_conjSubgroup, hv1]
  have hM' : conjSubgroup D.M g = conjSubgroup D.M (m * g) := by
    rw [← conjSubgroup_conjSubgroup, hM]
  have hcfg : s15T7Config (conjSubgroup D.M (m * g))
      (conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L ⊔
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g))
      (conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g)) F C K := by
    rw [← hE, ← hU, ← hM']
    exact ⟨hFab, hFM, hCF, hFN, hC, hUK, hKE, hmK, hFK, hmFC⟩
  exact h1 V₀ V L h hL _ _ _ (s15_T7_config_conj _ _ _ F C K (m * g) hcfg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
