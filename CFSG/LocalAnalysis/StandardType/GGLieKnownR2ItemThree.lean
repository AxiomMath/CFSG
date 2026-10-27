module

public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open
open scoped commutatorElement

private theorem induced_isTwoPower_of_isPGroup {G : Type*} [Group G] {K Y : Subgroup G}
    (hYK : Y ≤ Subgroup.normalizer (K : Set G)) (hY2 : IsPGroup 2 Y) {y : G} (hy : y ∈ Y) :
    ∃ k : ℕ, K.normalizerMonoidHom ⟨y, hYK hy⟩ ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hY2 ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have h1 : (⟨y, hYK hy⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [← map_pow, h1, map_one]

theorem ggRootNormInner_le_sup_centralizer_of_commutator {G : Type*} [Group G] {K R Y : Subgroup G}
    (hRK : R ≤ K) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) (hY2 : IsPGroup 2 Y)
    (hcomm : ⁅Y, K ⊓ Subgroup.normalizer (R : Set G)⁆ ≤
      pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)))
    (hI : GGRootNormInner (R.subgroupOf K)) :
    Y ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  intro y hy
  have hNK : (K ⊓ Subgroup.normalizer (R : Set G)).subgroupOf K =
      Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hRK]
  have hcommIn : ∀ n ∈ Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K),
      K.normalizerMonoidHom ⟨y, hYK hy⟩ n * n⁻¹ ∈
        pCoreOf 2 (Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K)) := by
    intro n hn
    rw [← hNK, GGRootNorm.pCoreOf_subgroupOf inf_le_left]
    have hnG : (n : G) ∈ Subgroup.normalizer (R : Set G) :=
      (GGRootNorm.mem_normalizer_subgroupOf_iff hRK n).mp hn
    have hmem : ⁅y, (n : G)⁆ ∈ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) :=
      hcomm (Subgroup.commutator_mem_commutator hy ⟨n.2, hnG⟩)
    change ((K.normalizerMonoidHom ⟨y, hYK hy⟩ n * n⁻¹ : K) : G) ∈
      pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G))
    have e : ((K.normalizerMonoidHom ⟨y, hYK hy⟩ n * n⁻¹ : K) : G) = ⁅y, (n : G)⁆ := by
      change y * (n : G) * y⁻¹ * (n : G)⁻¹ = ⁅y, (n : G)⁆
      simp only [commutatorElement_def]
    rw [e]
    exact hmem
  obtain ⟨k, hk⟩ := hI _ (induced_isTwoPower_of_isPGroup hYK hY2 hy)
    (GGRootNorm.mem_ggStab_iff.mp
      (GGRootNorm.normalizerMonoidHom_mem_ggStab (hYK hy) (hYR hy))) hcommIn
  exact GGRootNorm.mem_sup_centralizer_of_induced_inner (hYK hy) hk

end CFSG.StandardType.LieKnownR2
