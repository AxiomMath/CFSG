module

public import CFSG.LieType.Chevalley.OrthogonalFoldedWeyl
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace SmallCompOrder

section OneClass


variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem unionRoots_singleton_eq (i : KernelComponent χ) :
    unionRoots χ ({i} : Set (KernelComponent χ)) = componentRoots χ i := by
  ext α
  rw [mem_unionRoots_iff]
  simp

theorem unionRootSpan_singleton_eq (i : KernelComponent χ) :
    unionRootSpan K χ ({i} : Set (KernelComponent χ)) = componentRootSpan K χ i := by
  change rootSpan τ K (unionRoots χ ({i} : Set (KernelComponent χ))) = _
  rw [unionRoots_singleton_eq]
  rfl

theorem unionTorus_singleton_eq (i : KernelComponent χ) :
    unionTorus K χ ({i} : Set (KernelComponent χ)) = componentTorus K χ i := by
  change unionRootSpan K χ ({i} : Set (KernelComponent χ)) ⊓ torusGroup τ K = _
  rw [unionRootSpan_singleton_eq]
  rfl

theorem unionSimpleRoots_singleton_eq (i : KernelComponent χ) :
    unionSimpleRoots χ ({i} : Set (KernelComponent χ)) =
      (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ)) := by
  ext β
  simp [unionSimpleRoots]

theorem unionWeylGroup_singleton_eq (i : KernelComponent χ) :
    unionWeylGroup χ ({i} : Set (KernelComponent χ)) = componentWeylGroup (componentRoots χ i) := by
  change Subgroup.closure (rootReflection '' unionSimpleRoots χ ({i} : Set (KernelComponent χ))) =
    Subgroup.closure (rootReflection '' (simpleRoots (componentRoots χ i) : Set _))
  rw [unionSimpleRoots_singleton_eq]

end OneClass

section Cells


variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem rootWeylOne_lift_spec (J : Set (KernelComponent χ)) :
    ∀ β ∈ unionSimpleRoots χ J, rootWeylOne τ K β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
      rootWeylOne τ K β ∈ monomialSubgroup τ K ∧
      MapsRootLines (rootWeylOne τ K β) (rootReflection β) :=
  fun _ hβ => rootWeylOne_spec (isRoot_of_mem_unionSimpleRoots hβ)

theorem card_unionBorel_eq (J : Set (KernelComponent χ)) :
    Nat.card (unionBorel K χ J) =
      Nat.card (unionTorus K χ J) * Nat.card (unionUnipotent K χ J) := by
  have hbij : Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * p.2)
      ((unionTorus K χ J : Set (ModGL τ K)) ×ˢ (unionUnipotent K χ J : Set (ModGL τ K)))
      (unionBorel K χ J : Set (ModGL τ K)) := by
    refine ⟨fun p hp => ?_, fun p hp p' hp' h => ?_, fun x hx => ?_⟩
    · rw [coe_unionBorel]
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_eq_mul hp.1 hp'.1 hp.2 hp'.2 h
      exact Prod.ext h1 h2
    · rw [coe_unionBorel] at hx
      obtain ⟨t, ht, u, hu, rfl⟩ := hx
      exact ⟨(t, u), ⟨ht, hu⟩, rfl⟩
  calc Nat.card (unionBorel K χ J) = Nat.card ((unionTorus K χ J : Set (ModGL τ K)) ×ˢ
        (unionUnipotent K χ J : Set (ModGL τ K))) := Nat.card_congr hbij.equiv.symm
    _ = Nat.card (unionTorus K χ J) * Nat.card (unionUnipotent K χ J) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl

theorem card_unionUnipotent_eq (J : Set (KernelComponent χ)) :
    Nat.card (unionUnipotent K χ J) = Nat.card K ^ (posRoots (unionRoots χ J)).ncard :=
  card_rootSpan (fun _ hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα)
    fun _ hα _ hβ a b ha hb hr => nsmul_add_mem_posRoots_unionRoots hα hβ a b ha hb hr

theorem unionInversionRoots_closed (J : Set (KernelComponent χ)) (w : WeylGroup τ) :
    ∀ α ∈ unionInversionRoots χ J w, ∀ β ∈ unionInversionRoots χ J w, ∀ a b : ℕ, 1 ≤ a →
      1 ≤ b → IsRoot τ (a • α + b • β) → a • α + b • β ∈ unionInversionRoots χ J w := by
  intro α hα β hβ a b ha hb hr
  refine ⟨nsmul_add_mem_posRoots_unionRoots hα.1 hβ.1 a b ha hb hr, ?_⟩
  have h1 : w • (a • α + b • β) = a • (w • α) + b • (w • β) := by
    rw [smul_add, smul_comm w a α, smul_comm w b β]
  rw [h1, height_nsmul_add_nsmul]
  have h2 := hα.2
  have h3 := hβ.2
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem card_rootSpan_unionInversionRoots (J : Set (KernelComponent χ)) (w : WeylGroup τ) :
    Nat.card (rootSpan τ K (unionInversionRoots χ J w)) =
      Nat.card K ^ (unionInversionRoots χ J w).ncard :=
  card_rootSpan (fun _ hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα.1)
    (unionInversionRoots_closed J w)

theorem card_unionCell_eq (J : Set (KernelComponent χ)) {w : WeylGroup τ}
    (hw : w ∈ unionWeylGroup χ J) :
    Nat.card (unionCell K χ J (rootWeylOne τ K) w) =
      Nat.card (unionBorel K χ J) * Nat.card K ^ (unionInversionRoots χ J w).ncard := by
  have hn := rootWeylOne_lift_spec (K := K) J
  obtain ⟨g, hg⟩ := exists_mem_unionLifts hn hw
  rw [← doubleCoset_eq_unionCell hn hg]
  calc Nat.card ↥((unionBorel K χ J : Set (ModGL τ K)) * ({g} : Set (ModGL τ K)) *
        (unionBorel K χ J : Set (ModGL τ K))) =
        Nat.card ↥((unionBorel K χ J : Set (ModGL τ K)) ×ˢ
          (rootSpan τ K (unionInversionRoots χ J w) : Set (ModGL τ K))) :=
        Nat.card_congr (bijOn_mul_unionCell hn hw hg).equiv.symm
    _ = Nat.card (unionBorel K χ J) * Nat.card (rootSpan τ K (unionInversionRoots χ J w)) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl
    _ = _ := by rw [card_rootSpan_unionInversionRoots]

theorem card_unionRootSpan_eq [Finite K] (J : Set (KernelComponent χ)) :
    Nat.card (unionRootSpan K χ J) = Nat.card (unionTorus K χ J) *
      Nat.card K ^ (posRoots (unionRoots χ J)).ncard *
        ∑ᶠ w : unionWeylGroup χ J, Nat.card K ^ (unionInversionRoots χ J w).ncard := by
  classical
  have : Fintype (unionWeylGroup χ J) := Fintype.ofFinite _
  have hn := rootWeylOne_lift_spec (K := K) J
  have hU : (⋃ w ∈ unionWeylGroup χ J, unionCell K χ J (rootWeylOne τ K) w) =
      ⋃ w : unionWeylGroup χ J, unionCell K χ J (rootWeylOne τ K) w := by
    ext x
    simp only [Set.mem_iUnion, exists_prop, Subtype.exists]
  have e : (unionRootSpan K χ J : Set (ModGL τ K)) ≃
      Σ w : unionWeylGroup χ J, unionCell K χ J (rootWeylOne τ K) w := by
    rw [coe_unionRootSpan_eq_iUnion hn, hU]
    exact Set.unionEqSigmaOfDisjoint fun w w' h =>
      disjoint_unionCell hn fun h' => h (Subtype.ext h')
  calc Nat.card (unionRootSpan K χ J) =
        Nat.card (Σ w : unionWeylGroup χ J, unionCell K χ J (rootWeylOne τ K) w) :=
        Nat.card_congr e
    _ = ∑ w : unionWeylGroup χ J, Nat.card (unionCell K χ J (rootWeylOne τ K) w) :=
        Nat.card_sigma
    _ = _ := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [card_unionCell_eq J w.2, card_unionBorel_eq, card_unionUnipotent_eq]

theorem exists_card_componentRootSpan_eq [Finite K] (i : KernelComponent χ) :
    ∃ s : Finset (WeylGroup τ),
      (∀ w, w ∈ s ↔ w ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ))) ∧
      Nat.card (componentRootSpan K χ i) = Nat.card (componentTorus K χ i) *
        Nat.card K ^ (posRoots (componentRoots χ i)).ncard *
          ∑ w ∈ s, Nat.card K ^
            (unionInversionRoots χ ({i} : Set (KernelComponent χ)) w).ncard := by
  classical
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  refine ⟨Finset.univ.filter (· ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ))),
    fun w => by simp, ?_⟩
  have h := card_unionRootSpan_eq (K := K) ({i} : Set (KernelComponent χ))
  rw [unionRootSpan_singleton_eq, unionTorus_singleton_eq, unionRoots_singleton_eq] at h
  rw [h]
  congr 1
  rw [finsum_eq_sum_of_fintype]
  refine (Finset.sum_subtype (p := (· ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ)))) _
    (fun w => ?_) (fun w => Nat.card K ^
      (unionInversionRoots χ ({i} : Set (KernelComponent χ)) w).ncard)).symm
  simp

end Cells

end SmallCompOrder

end CFSG.StandardType
