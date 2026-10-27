module

public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem exists_commuting_faithful_of_check_of_ringChar_ne_two {K : Type} [Field K]
    (hK : ringChar K ≠ 2) (τ : Tag) {n : ℕ} (α : Fin n → Fin τ.rank → ℤ)
    (h : (∀ i, RootOps.isRootB τ (α i) = true) ∧
      ∀ i j, i ≠ j → iform (α i) (α j) = 0 ∧ RootOps.isRootB τ (α i + α j) = false ∧
        RootOps.isRootB τ (α i - α j) = false) :
    ∃ ι : Fin n → (SL2 K →* adjointGroup τ K), (∀ i, Function.Injective (ι i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL2 K, ι i A * ι j B = ι j B * ι i A := by
  have hroot : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (h.1 i)
  have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  refine ⟨fun i => (rootSL2 τ K (α i)).codRestrict (adjointGroup τ K)
    (exceptional_Lang_root_rank_one_data τ K (α i)).2.2.2.2.1, fun i A B hAB => ?_,
    fun i j hij A B => ?_⟩
  · exact ((exceptional_Lang_root_rank_one_data τ K (α i)).2.2.2.2.2.2.2.1 hK).1
      (congrArg Subtype.val hAB)
  · obtain ⟨h0, hp, hm⟩ := h.2 i j hij
    exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
      (hroot i) (hroot j) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)

theorem G2_two_commuting_faithful_SL2 (K : Type) [Field K] (hK : ringChar K ≠ 2) :
    ∃ ι₁ ι₂ : SL2 K →* adjointGroup .G2 K, Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      ∀ A B : SL2 K, ι₁ A * ι₂ B = ι₂ B * ι₁ A := by
  obtain ⟨ι, hinj, hcomm⟩ := exists_commuting_faithful_of_check_of_ringChar_ne_two hK .G2
    ![![1, 0], ![1, 2]] (by decide +kernel)
  exact ⟨ι 0, ι 1, hinj 0, hinj 1, hcomm 0 1 (by decide)⟩

end CFSG.RankThree.Chevalley
