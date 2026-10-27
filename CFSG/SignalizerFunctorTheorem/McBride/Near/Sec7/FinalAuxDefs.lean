module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

variable {G : Type*} [Group G]

structure IsIDP {ι : Type*} (X : ι → Subgroup G) (K : Subgroup G) : Prop where
  commute : ∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, Commute x y
  indep : iSupIndep X
  iSup_eq : ⨆ i, X i = K

namespace IsIDP

variable {ι : Type*} {X : ι → Subgroup G} {K : Subgroup G}

theorem le (h : IsIDP X K) (i : ι) : X i ≤ K := h.iSup_eq ▸ le_iSup X i

theorem inf_eq_bot (h : IsIDP X K) {i j : ι} (hij : i ≠ j) : X i ⊓ X j = ⊥ :=
  disjoint_iff.mp (h.indep.pairwiseDisjoint hij)

theorem injective (h : IsIDP X K) (hne : ∀ i, X i ≠ ⊥) : Function.Injective X := by
  intro i j hij
  by_contra hne'
  apply hne i
  have := h.inf_eq_bot hne'
  rwa [← hij, inf_idem] at this

theorem isDirectProduct_range (h : IsIDP X K) : IsDirectProduct (Set.range X) K where
  commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact h.commute i j (fun hij => hne (hij ▸ rfl))
  indep := h.indep.sSupIndep_range
  sSup_eq := by rw [sSup_range, h.iSup_eq]

end IsIDP

theorem IsIDP.of_isDirectProduct_range {ι : Type*} {X : ι → Subgroup G} {K : Subgroup G}
    (h : IsDirectProduct (Set.range X) K) (hinj : Function.Injective X) : IsIDP X K where
  commute i j hij := h.commute (X i) ⟨i, rfl⟩ (X j) ⟨j, rfl⟩ (fun e => hij (hinj e))
  indep := by
    have h1 := (sSupIndep_iff (Set.range X)).mp h.indep
    exact h1.comp (f := fun i => (⟨X i, i, rfl⟩ : Set.range X)) (fun i j e =>
      hinj (congrArg Subtype.val e))
  iSup_eq := by rw [← sSup_range, h.sSup_eq]

theorem IsDirectProduct.isIDP {S : Set (Subgroup G)} {K : Subgroup G} (h : IsDirectProduct S K) :
    IsIDP (fun J : S => (J : Subgroup G)) K where
  commute i j hij := h.commute i i.2 j j.2 (fun e => hij (Subtype.ext e))
  indep := (sSupIndep_iff S).mp h.indep
  iSup_eq := by rw [← sSup_eq_iSup', h.sSup_eq]

theorem IsIDP.comp {ι ι' : Type*} {X : ι → Subgroup G} {K : Subgroup G} (h : IsIDP X K)
    (e : ι' ≃ ι) : IsIDP (X ∘ e) K where
  commute i j hij := h.commute (e i) (e j) (fun e' => hij (e.injective e'))
  indep := h.indep.comp e.injective
  iSup_eq := by rw [← h.iSup_eq]; exact e.iSup_comp

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
