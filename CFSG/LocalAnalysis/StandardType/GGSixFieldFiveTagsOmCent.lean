module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsOmFree
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular

public section

namespace CFSG.StandardType

namespace FieldFiveOm

open QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores LayerCores.OrthSplit LayerFacts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_subCoreFamily_orthCent_fix (hQ : (polarBilin Q).Nondegenerate)
    {A : Subgroup (V ≃ₗ[K] V)} (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hAc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) (hA5 : ∀ g ∈ A, g ^ 5 = 1) (h5 : 5 < Nat.card A) :
    ∃ (β : Type) (S : β → Subgroup (V ≃ₗ[K] V)),
      IsSubCoreFamily (Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧
      ∀ c, ∃ T ∈ A, T ≠ 1 ∧ ∀ M ∈ S c, ∀ v : V, M (T v - v) = T v - v := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact FieldFiveSp.natCast_card_ne_zero_of_pow_five fun g =>
      Subtype.ext (by simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hA5 _ g.2)
  obtain ⟨β₀, S₀, hS₀⟩ := ggOrthRegularCoreInput_holds K (fixSp A) (Q.restrict (fixSp A))
    (nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO))
  have hA₁O : freeGroup A ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp A)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y =>
      map_of_mem (hAO (Subgroup.mem_subgroupOf.mp ha)) (y : V)
  have hA₁c : ∀ g ∈ freeGroup A, ∀ h ∈ freeGroup A, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp ha'))
  have hA₁5 : ∀ g ∈ freeGroup A, g ^ 5 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have h1 : a ^ 5 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hA5 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [h1, map_one]
  have hres : ∀ g ∈ A, ∀ hg : g ∈ stab A, ∀ v : V,
      g v = avg A v + (restrFree A ⟨g, hg⟩ ⟨v - avg A v, sub_avg_mem_freeSp hA v⟩ : V) := by
    intro g hgA hg v
    rw [coe_restrFree_apply]
    show g v = avg A v + g (v - avg A v)
    rw [map_sub, apply_avg hgA, add_sub_cancel]
  have hA₁card : 5 < Nat.card (freeGroup A) := by
    have := finite_linearEquiv (K := K) (V := freeSp A)
    let f : A → freeGroup A := fun a => ⟨restrFree A ⟨a, le_stab a.2⟩,
      ⟨⟨a, le_stab a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩⟩
    have hf : Function.Injective f := by
      intro a a' haa
      have h1 : restrFree A ⟨a, le_stab a.2⟩ = restrFree A ⟨a', le_stab a'.2⟩ :=
        congrArg Subtype.val haa
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      rw [hres a a.2 (le_stab a.2) v, hres a' a'.2 (le_stab a'.2) v, h1]
    exact lt_of_lt_of_le h5 (Nat.card_le_card_of_injective f hf)
  have hA₁free : ∀ w : freeSp A, (∀ a ∈ freeGroup A, a w = w) → w = 0 := by
    intro w hw
    have h1 : (w : V) ∈ fixSp A := (mem_fixSp_iff hA).mpr fun a ha =>
      congrArg Subtype.val (hw (restrFree A ⟨a, le_stab ha⟩)
        ⟨⟨a, le_stab ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
    exact Subtype.ext ((Submodule.disjoint_def.mp (isCompl_fixSp_freeSp hA).disjoint) _ h1 w.2)
  obtain ⟨β₁, S₁, hS₁, hS₁T⟩ := exists_coreFamily_orthFree_fix
    (nondegenerate_polarBilin_restrict (polarNondegOn_freeSp hQ hA hAO)) hA₁O hA₁c hA₁5 hA₁card
    hA₁free
  refine ⟨β₀ ⊕ β₁, fun c => (prodFamily S₀ S₁ c).map (split hA), ?_, ?_⟩
  · rw [centralizer_eq_map_split hA hAO]
    exact (hS₀.prod hS₁.toSub).map _ (split_injective hA)
  have hTv : ∀ T ∈ A, ∀ v : V, T v - v ∈ freeSp A := fun T hT v => by
    rw [LinearMap.mem_ker, map_sub, avg_apply_apply hT, sub_self]
  rintro (c | c)
  ·
    obtain ⟨T, hTA, hT1⟩ := exists_ne_one hA5 h5
    refine ⟨T, hTA, hT1, ?_⟩
    rintro _ ⟨_, ⟨m, -, rfl⟩, rfl⟩ v
    have h1 := split_apply_free hA (MonoidHom.inl _ _ m) ⟨T v - v, hTv T hTA v⟩
    simpa using h1
  ·
    obtain ⟨T₁, hT₁A, hT₁1, hT₁M⟩ := hS₁T c
    obtain ⟨⟨T, hTs⟩, hTA, rfl⟩ := hT₁A
    have hTA' : T ∈ A := Subgroup.mem_subgroupOf.mp hTA
    refine ⟨T, hTA', fun h => hT₁1 ?_, ?_⟩
    · have h1 : (⟨T, hTs⟩ : stab A) = 1 := Subtype.ext h
      rw [h1, map_one]
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩ v
    set v₁ : freeSp A := ⟨v - avg A v, sub_avg_mem_freeSp hA v⟩ with hv₁
    have e1 : (⟨T v - v, hTv T hTA' v⟩ : freeSp A) = restrFree A ⟨T, hTs⟩ v₁ - v₁ := by
      apply Subtype.ext
      rw [Submodule.coe_sub, coe_restrFree_apply, hv₁]
      show T v - v = T (v - avg A v) - (v - avg A v)
      rw [map_sub, apply_avg hTA']
      abel
    have h1 : split hA (MonoidHom.inr _ _ m) (T v - v) = (m ⟨T v - v, hTv T hTA' v⟩ : V) :=
      split_apply_free hA (MonoidHom.inr _ _ m) ⟨T v - v, hTv T hTA' v⟩
    rw [h1, e1, hT₁M m hm v₁]
    exact congrArg Subtype.val e1.symm

end FieldFiveOm

end CFSG.StandardType
