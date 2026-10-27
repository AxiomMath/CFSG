module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmegaFree
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmegaRegular

public section

namespace CFSG.StandardType

namespace LayerPDiv

open QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores LayerCores.OrthSplit

theorem dvd_card_prodFamily {G₁ G₂ : Type*} [Group G₁] [Group G₂] {β₁ β₂ : Type}
    (S₁ : β₁ → Subgroup G₁) (S₂ : β₂ → Subgroup G₂) {p : ℕ} (h₁ : ∀ c, p ∣ Nat.card (S₁ c))
    (h₂ : ∀ c, p ∣ Nat.card (S₂ c)) (c : β₁ ⊕ β₂) : p ∣ Nat.card (prodFamily S₁ S₂ c) := by
  rcases c with c | c
  · show p ∣ Nat.card ((S₁ c).map (MonoidHom.inl G₁ G₂))
    rw [Subgroup.card_map_of_injective (fun a b h => congrArg Prod.fst h)]
    exact h₁ c
  · show p ∣ Nat.card ((S₂ c).map (MonoidHom.inr G₁ G₂))
    rw [Subgroup.card_map_of_injective (fun a b h => congrArg Prod.snd h)]
    exact h₂ c

theorem exists_subCoreFamily_orthCent_pDiv {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (V ≃ₗ[K] V)}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card A)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) :
    ∃ (β : Type) (S : β → Subgroup (V ≃ₗ[K] V)),
      IsSubCoreFamily (Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧ ∀ c, p ∣ Nat.card (S c) := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨β₀, S₀, hS₀, hp₀⟩ := exists_subCoreFamily_orthRegular_pDiv (Q.restrict (fixSp A))
    (nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO)) hp hp2 hpK
  have hA₁O : freeGroup A ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp A)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y =>
      map_of_mem (hAO (Subgroup.mem_subgroupOf.mp ha)) (y : V)
  have hA₁odd : Odd (Nat.card (freeGroup A)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_stab).toEquiv]
    exact hodd
  have hA₁free : ∀ w : freeSp A, (∀ a ∈ freeGroup A, a w = w) → w = 0 := by
    intro w hw
    have h1 : (w : V) ∈ fixSp A := (mem_fixSp_iff hA).mpr fun a ha =>
      congrArg Subtype.val (hw (restrFree A ⟨a, le_stab ha⟩)
        ⟨⟨a, le_stab ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
    exact Subtype.ext ((Submodule.disjoint_def.mp (isCompl_fixSp_freeSp hA).disjoint) _ h1 w.2)
  obtain ⟨β₁, S₁, hS₁, hp₁⟩ := exists_coreFamily_orthFree_pDiv
    (nondegenerate_polarBilin_restrict (polarNondegOn_freeSp hQ hA hAO)) hA₁O hA₁odd hA₁free hpK
  refine ⟨β₀ ⊕ β₁, fun c => (prodFamily S₀ S₁ c).map (split hA), ?_, fun c => ?_⟩
  · rw [centralizer_eq_map_split hA hAO]
    exact (hS₀.prod hS₁.toSub).map _ (split_injective hA)
  · rw [Subgroup.card_map_of_injective (split_injective hA)]
    exact dvd_card_prodFamily S₀ S₁ hp₀ hp₁ c

end LayerPDiv

end CFSG.StandardType
