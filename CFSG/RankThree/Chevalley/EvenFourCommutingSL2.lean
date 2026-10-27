module

public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem exists_four_commuting_faithful_of_check {K : Type} [Field K] [CharP K 2] (τ : Tag)
    (α : Fin 4 → Fin τ.rank → ℤ)
    (h : (∀ i, RootOps.isRootB τ (α i) = true) ∧
      ∀ i j, i ≠ j → iform (α i) (α j) = 0 ∧ RootOps.isRootB τ (α i + α j) = false ∧
        RootOps.isRootB τ (α i - α j) = false) :
    ∃ ι : Fin 4 → (SL2 K →* adjointGroup τ K), (∀ i, Function.Injective (ι i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL2 K, ι i A * ι j B = ι j B * ι i A := by
  have hroot : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (h.1 i)
  have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  refine ⟨fun i => (rootSL2 τ K (α i)).codRestrict (adjointGroup τ K)
    (exceptional_Lang_root_rank_one_data τ K (α i)).2.2.2.2.1, fun i A B hAB => ?_,
    fun i j hij A B => ?_⟩
  · exact (even_Chevalley_pinned_root_SL2_maps τ K (hroot i)).1 (congrArg Subtype.val hAB)
  · obtain ⟨h0, hp, hm⟩ := h.2 i j hij
    exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
      (hroot i) (hroot j) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)

theorem even_higher_ordinary_exceptional_four_commuting_faithful_SL2 (K : Type) [Field K]
    [CharP K 2] (τ : Tag) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ ι : Fin 4 → (SL2 K →* adjointGroup τ K), (∀ i, Function.Injective (ι i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL2 K, ι i A * ι j B = ι j B * ι i A := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact exists_four_commuting_faithful_of_check .F4
      ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]] (by decide +kernel)
  · exact exists_four_commuting_faithful_of_check .E6
      ![![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]]
      (by decide +kernel)
  · exact exists_four_commuting_faithful_of_check .E7
      ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0]] (by decide +kernel)
  · exact exists_four_commuting_faithful_of_check .E8
      ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 1, 1, 1, 0, 0, 0, 0]] (by decide +kernel)

end CFSG.RankThree.Chevalley
