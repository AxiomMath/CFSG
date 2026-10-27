module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qf
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus nondegenerate_polarBilin_quadPlus)
open Module

private theorem s16k_exists_two_nonzero_of_two_le_finrank {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {W : Submodule K V}
    (h : 2 ≤ finrank K W) :
    ∃ u₁ u₂ : V, u₁ ∈ W ∧ u₂ ∈ W ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₁ ≠ u₂ := by
  have hbot : W ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h
    omega
  obtain ⟨u₁, hu₁W, hu₁ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hle : K ∙ u₁ ≤ W := (Submodule.span_singleton_le_iff_mem u₁ W).mpr hu₁W
  have hne : K ∙ u₁ ≠ W := by
    intro heq
    have h1 : finrank K (K ∙ u₁) = 1 := finrank_span_singleton hu₁ne
    rw [heq] at h1
    omega
  have hlt : K ∙ u₁ < W := lt_of_le_of_ne hle hne
  obtain ⟨u₂, hu₂W, hu₂notin⟩ :=
    Set.exists_of_ssubset (SetLike.coe_ssubset_coe.mpr hlt)
  refine ⟨u₁, u₂, hu₁W, hu₂W, hu₁ne, ?_, ?_⟩
  · exact fun h0 => hu₂notin (h0 ▸ Submodule.zero_mem (K ∙ u₁))
  · exact fun h1 => hu₂notin (h1 ▸ Submodule.mem_span_singleton_self u₁)

private theorem s16k_exists_two_moves_of_even {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : V ≃ₗ[K] V} (hG : G ≠ 1)
    (heven : Even (finrank K (commSpace G))) :
    ∃ u₁ u₂ : V, u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₁ ≠ u₂ ∧
      (∃ v, G v - v = u₁) ∧ (∃ v, G v - v = u₂) := by
  have hpos : 1 ≤ finrank K (commSpace G) := one_le_finrank_commSpace hG
  have h2 : 2 ≤ finrank K (commSpace G) := by
    rcases heven with ⟨k, hk⟩
    omega
  obtain ⟨u₁, u₂, hu₁W, hu₂W, hu₁, hu₂, hne⟩ :=
    s16k_exists_two_nonzero_of_two_le_finrank h2
  exact ⟨u₁, u₂, hu₁, hu₂, hne, mem_commSpace.mp hu₁W, mem_commSpace.mp hu₂W⟩

theorem s16k_statedOmega_moves {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {g : ↥(StatedOmega (StatedQuadPlus 4 K))} (hg1 : g ≠ 1) :
    ∃ u₁ u₂ : Fin 4 ⊕ Fin 4 → K, u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₁ ≠ u₂ ∧
      (∃ v : Fin 4 ⊕ Fin 4 → K,
        u₁ = ((g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).mulVec v - v) ∧
      (∃ v : Fin 4 ⊕ Fin 4 → K,
        u₂ = ((g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).mulVec v - v) := by
  have hQ : (quadPlus 4 K).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 4 K
  have hcomm : toLinEquiv (Fin 4 ⊕ Fin 4) K (g : GL (Fin 4 ⊕ Fin 4) K) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ := by
    have h : (g : GL (Fin 4 ⊕ Fin 4) K) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆.comap
            (toLinEquiv (Fin 4 ⊕ Fin 4) K).toMonoidHom := by
      rw [← statedOmega_eq_comap (coe_quadPlus 4 K)]
      exact g.2
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at h
    exact h
  rw [← Subgroup.map_subtype_commutator] at hcomm
  obtain ⟨G₀, hG₀comm, hG₀eq⟩ := Subgroup.mem_map.mp hcomm
  have hker := Abelianization.commutator_subset_ker
    (dicksonHom (quadPlus 4 K) hQ) hG₀comm
  rw [MonoidHom.mem_ker, dicksonHom_apply] at hker
  have heven₀ : Even (finrank K (commSpace
      (G₀ : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)))) := by
    rw [← ZMod.natCast_eq_zero_iff_even]
    exact ofAdd_eq_one.mp hker
  have heven : Even (finrank K (commSpace
      (toLinEquiv (Fin 4 ⊕ Fin 4) K (g : GL (Fin 4 ⊕ Fin 4) K)))) := by
    rw [← hG₀eq]
    exact heven₀
  have hG1 : toLinEquiv (Fin 4 ⊕ Fin 4) K (g : GL (Fin 4 ⊕ Fin 4) K) ≠ 1 := by
    intro h
    apply hg1
    apply Subtype.ext
    exact (toLinEquiv (Fin 4 ⊕ Fin 4) K).injective (by
      rw [h]
      simp)
  obtain ⟨u₁, u₂, hu₁, hu₂, hne, ⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ :=
    s16k_exists_two_moves_of_even hG1 heven
  refine ⟨u₁, u₂, hu₁, hu₂, hne, ⟨v₁, ?_⟩, ⟨v₂, ?_⟩⟩
  · rw [← hv₁, toLinEquiv_apply]
  · rw [← hv₂, toLinEquiv_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
