module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmCent

public section

namespace CFSG.StandardType

namespace OmNonsplit

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  LayerCores LayerCores.OrthSplit LayerFacts
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_subCoreFamily_orthCent_fix (hQ : (polarBilin Q).Nondegenerate) {a : V ≃ₗ[K] V}
    (haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hap : a ^ p = 1) [Fintype (Subgroup.zpowers a)]
    (hA : (Fintype.card (Subgroup.zpowers a) : K) ≠ 0) :
    ∃ (β : Type) (S : β → Subgroup (V ≃ₗ[K] V)),
      IsSubCoreFamily (Subgroup.centralizer (Subgroup.zpowers a : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧
      ∀ c, ¬ p ∣ Nat.card (S c) →
        ∃ T : Subgroup (fixSp (Subgroup.zpowers a) ≃ₗ[K] fixSp (Subgroup.zpowers a)),
          CFSG.IsQuasisimple T ∧ CFSG.Assembly.IsSubnormal T
            (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp (Subgroup.zpowers a)))) ∧
          ¬ p ∣ Nat.card T ∧ S c = T.map (extFix hA) := by
  classical
  have hAO : (Subgroup.zpowers a) ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr haO
  obtain ⟨β₀, S₀, hS₀⟩ := ggOrthRegularCoreInput_holds K (fixSp (Subgroup.zpowers a))
    (Q.restrict (fixSp (Subgroup.zpowers a)))
    (nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO))
  set a₁ := restrFree (Subgroup.zpowers a) ⟨a, le_stab (Subgroup.mem_zpowers a)⟩ with ha₁
  have hfg : freeGroup (Subgroup.zpowers a) = Subgroup.zpowers a₁ := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hg)
      have hgk : g = (⟨a, le_stab (Subgroup.mem_zpowers a)⟩ : stab (Subgroup.zpowers a)) ^ k :=
        Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [hgk, map_zpow]
      exact Subgroup.zpow_mem_zpowers a₁ k
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨a, le_stab (Subgroup.mem_zpowers a)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a), rfl⟩
  have ha₁O :
      a₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp (Subgroup.zpowers a))) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y => map_of_mem haO (y : V)
  have ha₁p : a₁ ^ p = 1 := by
    rw [ha₁, ← map_pow]
    have h : (⟨a, le_stab (Subgroup.mem_zpowers a)⟩ : stab (Subgroup.zpowers a)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hap)
    rw [h, map_one]
  have ha₁free : ∀ w : freeSp (Subgroup.zpowers a), a₁ w = w → w = 0 := by
    intro w hw
    have hw' : a (w : V) = w := congrArg Subtype.val hw
    have h1 : (w : V) ∈ fixSp (Subgroup.zpowers a) := (mem_fixSp_iff hA).mpr fun g hg => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_apply_eq_self hw' k
    exact Subtype.ext ((Submodule.disjoint_def.mp (isCompl_fixSp_freeSp hA).disjoint) _ h1 w.2)
  obtain ⟨β₁, S₁, hS₁, hp₁⟩ := exists_coreFamily_orthFree_dvd
    (nondegenerate_polarBilin_restrict (polarNondegOn_freeSp hQ hA hAO)) ha₁O hp hp2 ha₁p
    ha₁free
  have hC₁ : freeCent (Subgroup.zpowers a) Q = Subgroup.centralizer (Subgroup.zpowers a₁ : Set _) ⊓
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp (Subgroup.zpowers a))) := by
    simp only [freeCent, hfg]
  have hinl : Function.Injective (MonoidHom.inl
      (fixSp (Subgroup.zpowers a) ≃ₗ[K] fixSp (Subgroup.zpowers a))
      (freeSp (Subgroup.zpowers a) ≃ₗ[K] freeSp (Subgroup.zpowers a))) :=
    fun _ _ h => congrArg Prod.fst h
  have hinr : Function.Injective (MonoidHom.inr
      (fixSp (Subgroup.zpowers a) ≃ₗ[K] fixSp (Subgroup.zpowers a))
      (freeSp (Subgroup.zpowers a) ≃ₗ[K] freeSp (Subgroup.zpowers a))) :=
    fun _ _ h => congrArg Prod.snd h
  refine ⟨β₀ ⊕ β₁, fun c => (prodFamily S₀ S₁ c).map (split hA), ?_, ?_⟩
  · rw [centralizer_eq_map_split hA hAO, hC₁]
    exact (hS₀.prod hS₁.toSub).map _ (split_injective hA)
  · rintro (c | c) hpc
    · simp only [prodFamily, Sum.elim_inl] at hpc ⊢
      refine ⟨S₀ c, hS₀.2.2.1 c, hS₀.2.1 c, fun h => hpc ?_, ?_⟩
      · rw [Subgroup.card_map_of_injective (split_injective hA),
          Subgroup.card_map_of_injective hinl]
        exact h
      · rw [Subgroup.map_map, extFix]
    · exfalso
      apply hpc
      simp only [prodFamily, Sum.elim_inr]
      rw [Subgroup.card_map_of_injective (split_injective hA),
        Subgroup.card_map_of_injective hinr]
      exact hp₁ c

end OmNonsplit

end CFSG.StandardType
