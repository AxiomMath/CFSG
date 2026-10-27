module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.Quasithin.EmptyFaithful.R3c16ReeA

public section

namespace CFSG.Quasithin.R3c16

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup.X6

theorem isPerfect_SL2_of_four_le {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect (SL2 F) := by
  have := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ : Finset F).card by
      rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩

section Tri

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem triality_threeElement_mem_sup_block
    (σ : K ≃+* K) (h3 : ¬ 3 ∣ Nat.card K - 1)
    (h4 : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a))
    {M : Subgroup (ModGL TwistTag.D4.tag K)}
    (hMC : M ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hUM : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ M)
    (hMne : M ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {y : ModGL TwistTag.D4.tag K} (hy : y ∈ M) {k : ℕ} (hk : y ^ (3 ^ k) = 1) (hy1 : y ≠ 1) :
    ∃ L : Subgroup (ModGL TwistTag.D4.tag K), Group.IsPerfect ↥L ∧ L ≤ M ∧
      y ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊔ L := by
  classical
  have hU2 : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
    (isPGroup_posUnipotent (K := K) 2 TwistTag.D4.tag).to_le
      (inf_le_left : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ _)
  obtain ⟨hle, hiff, -⟩ :=
    fixed_positive_root_overgroup_parabolic_containment TwistTag.D4 K σ hMC hUM
  set J : Set (Fin TwistTag.D4.foldedTag.rank) :=
    {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈ M}
    with hJ
  by_cases hJe : J = ∅
  · exfalso
    rw [hJe, graphFixedParabolic_empty] at hle
    have hyU : y ^ (Nat.card K - 1) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
      pow_card_sub_one_mem_graphFixedPosUnipotent σ.surjective (hle hy)
    exact hy1 (eq_one_of_isPGroup_two_of_threePow hU2 (mem_of_pow_mem_of_threePow hk h3 hyU) hk)
  · obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.2 hJe
    have hJsub : J ⊆ {a₀} := by
      intro a ha
      by_contra hne
      apply hMne
      apply hiff.1
      refine Set.eq_univ_of_forall fun i => ?_
      have h2 : ∀ x y z : Fin TwistTag.D4.foldedTag.rank, x ≠ y → z = x ∨ z = y := by decide
      rcases h2 a a₀ i (fun h => hne (by rw [h]; exact Set.mem_singleton _)) with rfl | rfl
      · exact ha
      · exact ha₀
    have hMP : M ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a₀} :=
      hle.trans (sup_le_sup_left (Subgroup.closure_mono (Set.image_mono hJsub)) _)
    have hyP : y ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
        fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ := by
      rw [← graphFixedParabolic_singleton_eq_sup σ.surjective]
      exact hMP hy
    have hexp : ∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
        h ^ (Nat.card K - 1) = 1 := fun h hh =>
      pow_card_sub_one_eq_one_of_mem_diagonalGroup
        (torusGroup_le_diagonalGroup (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1)
    have hyN : y ^ (Nat.card K - 1) ∈ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ :=
      pow_mem_sup_of_pow_eq_one (W := fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀)
        (H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
        (graphFixedRootTorus_le_normalizer_fixedPosWeylGroup a₀) hexp
        (by rw [sup_comm]; exact hyP)
    have hyN' : y ∈ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ :=
      mem_of_pow_mem_of_threePow hk h3 hyN
    obtain ⟨R, hRu, hRv, hRH, hRW, hn, hrange, -, -, -⟩ :=
      exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom a₀
    have hnL : canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection a₀) ∈ R.range :=
      ⟨WSL, by rw [hRW, hn]⟩
    have hperf : Group.IsPerfect ↥R.range := by
      have := isPerfect_SL2_of_four_le (h4 a₀)
      exact Group.IsPerfect.range R
    have hNle : fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ ≤
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊔ R.range :=
      sup_le_sup_left ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hnL)) _
    have hLN : R.range ≤ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ := by
      rw [hrange]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact graphFixedPosUnipotent_le_fixedPosWeylGroup a₀
          (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom a₀ c)
      · exact orbitY_mem_fixedPosWeylGroup a₀ c
    have hNM : fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ ≤ M :=
      sup_le hUM ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ha₀))
    exact ⟨R.range, hperf, hLN.trans hNM, hNle hyN'⟩

end Tri

end CFSG.Quasithin.R3c16
