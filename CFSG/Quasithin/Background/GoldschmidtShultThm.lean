module

public import CFSG.Quasithin.Background.GoldschmidtShultCore
public import CFSG.Quasithin.Background.GoldschmidtShultLink
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerDischarge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ShultMilestoneAssembly
public import CFSG.Quasithin.Background.GoldschmidtShultFixed

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open CFSG.QuasithinUnique CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore

theorem exists_sylow_of_isSylowTwoOf_top {G : Type*} [Group G] {T : Subgroup G}
    (h : IsSylowTwoOf T ⊤) : ∃ P : Sylow 2 G, (P : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have h1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    simpa [h1] using h.2.2
  exact ⟨h.2.1.toSylow hidx, rfl⟩

theorem shult_stronglyEmbedded
    (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (V : Subgroup G)
    (hVT : V ≤ (T : Subgroup G)) (hV : V ≠ ⊥) (hVel : IsElemAbelian 2 V)
    (hclosed : fusionStronglyClosed (V : Set G) (T : Subgroup G)) (hTI : fusionIsTI V)
    (hnormal : ¬ V.Normal) :
    fusionStronglyEmbedded ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalClosure (V : Set G))) :=
  strongly_closed_TI_embedding_from_local_criterion_and_smaller_recognition (Nat.card G)
    Nat.card_pos
    (bounded_criterion_of_no_least_failure (not_minimalLocalFailure_of_theoremTwo
      (HighRankPair.theoremTwo_of_unitaryMonomial UnitaryPairIndex.unitaryMonomialTheorem)) _)
    (bounded_rank_one_recognition _) G le_rfl T V hVT hV hVel hclosed hTI hnormal

theorem shult_core
    (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (V : Subgroup G)
    (hVT : V ≤ (T : Subgroup G)) (hV : V ≠ ⊥) (hVel : IsElemAbelian 2 V)
    (hclosed : fusionStronglyClosed (V : Set G) (T : Subgroup G)) (hTI : fusionIsTI V)
    (hnormal : ¬ V.Normal) :
    ShultCoreConclusion (T : Subgroup G) V :=
  shult_core_of_stronglyEmbedded T hVT hV hVel hclosed
    (shult_stronglyEmbedded G T V hVT hV hVel hclosed hTI hnormal)

theorem shultFusionTheorem :
    ∀ (G : Type) [Group G] [Finite G] (T V : Subgroup G),
      IsSylowTwoOf T ⊤ → V ≤ T → V ≠ ⊥ → IsElemAbelian 2 V →
        fusionStronglyClosed (V : Set G) T → fusionIsTI V → ¬ V.Normal → ShultConclusion T V := by
  intro G _ _ T V hT hVT hV hVel hclosed hTI hnormal
  obtain ⟨P, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases shult_core G P V hVT hV hVel hclosed hTI hnormal with ⟨h2, hL⟩ | ⟨-, hH, hΩ⟩
  · exact Or.inl ⟨h2, hL⟩
  · obtain ⟨f, hf, hQ⟩ := benderQuasisimple_of_hull (L := Subgroup.normalClosure (V : Set G)) hT
      Subgroup.le_normalClosure hVel hH hΩ
    exact Or.inr ⟨f, hf, hQ, hΩ⟩

theorem isSylowTwoOf_top_of_sylow {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) :
    IsSylowTwoOf (T : Subgroup G) ⊤ := by
  refine ⟨le_top, T.isPGroup', ?_⟩
  have h1 : ((T : Subgroup G).subgroupOf ⊤).index = (T : Subgroup G).index :=
    Subgroup.relIndex_top_right _
  rw [h1]
  exact T.not_dvd_index

theorem shultI85Part1 :
    ShultI85Part1 := by
  intro G _ _ M V h
  obtain ⟨T, hVT, hTM, hclosed, hTI, hnormal⟩ := h.shult_hypotheses
  have hT := isSylowTwoOf_top_of_sylow T
  rcases shultFusionTheorem G T V hT hVT h.2.1 h.2.2.2.2.1 hclosed hTI hnormal with
    ⟨h2, hL⟩ | ⟨f, hf, hQ, hΩ⟩
  · exact Or.inl ⟨h2, hL⟩
  · have hB := shult_stronglyEmbedded G T V hVT h.2.1 h.2.2.2.2.1 hclosed hTI hnormal
    have hmeet : M ⊓ Subgroup.normalClosure (V : Set G) =
        Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalClosure (V : Set G) := by
      rw [h.normalizer_eq]
    refine Or.inr ⟨f, hf, hQ, ⟨T ⊓ Subgroup.normalClosure (V : Set G),
      isSylowTwoOf_inf_normal hT, hΩ⟩, hmeet, ?_⟩
    rw [hmeet]
    have hsub : (Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalClosure (V : Set G)).subgroupOf
        (Subgroup.normalClosure (V : Set G)) =
        (Subgroup.normalizer (V : Set G)).subgroupOf (Subgroup.normalClosure (V : Set G)) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hsub]
    exact hB

end CFSG.Quasithin.Shult
