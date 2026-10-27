module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoExcDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

@[expose] def levTwoS3b_nodeSpan {τ : Tag} (K : KacData τ) (D : Finset (Option (Fin τ.rank))) :
    Submodule ℚ (Fin τ.rank → ℚ) :=
  Submodule.span ℚ (toRat '' (K.extRoot '' (D : Set (Option (Fin τ.rank)))))

theorem levTwoS3b_combo_mem_nodeSpan {τ : Tag} (K : KacData τ) (D : Finset (Option (Fin τ.rank)))
    (n : Option (Fin τ.rank) → ℕ) (hn : ∀ x, n x ≠ 0 → x ∈ D) :
    toRat (K.combo n) ∈ levTwoS3b_nodeSpan K D := by
  unfold KacData.combo
  rw [map_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : n x = 0
  · simp [hx]
  · have hxD : x ∈ D := hn x hx
    rw [map_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨K.extRoot x, ⟨x, hxD, rfl⟩, rfl⟩)

theorem levTwoS3b_rootsOf_subset_nodeSpan {τ : Tag} (K : KacData τ) (D : Finset (Option (Fin τ.rank))) :
    ∀ γ ∈ K.rootsOf D, toRat γ ∈ levTwoS3b_nodeSpan K D := by
  rintro γ ⟨-, n, hn, hγ | hγ⟩
  · rw [hγ]
    exact levTwoS3b_combo_mem_nodeSpan K D n hn
  · rw [hγ, map_neg]
    exact Submodule.neg_mem _ (levTwoS3b_combo_mem_nodeSpan K D n hn)

theorem levTwoS3b_finrank_nodeSpan_le {τ : Tag} (K : KacData τ) (D : Finset (Option (Fin τ.rank))) :
    Module.finrank ℚ (levTwoS3b_nodeSpan K D) ≤ D.card := by
  let t : Finset (Fin τ.rank → ℚ) := D.attach.image (fun x : ↥D => toRat (K.extRoot x.1))
  have ht : (t : Set (Fin τ.rank → ℚ)) =
      toRat '' (K.extRoot '' (D : Set (Option (Fin τ.rank)))) := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨K.extRoot x.1, ⟨x.1, x.2, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨x, hx, rfl⟩, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
  have htcard : t.card ≤ D.card := by
    calc t.card ≤ D.attach.card := Finset.card_image_le
      _ = D.card := Finset.card_attach
  rw [levTwoS3b_nodeSpan, ← ht]
  exact (finrank_span_finset_le_card t).trans htcard

theorem levTwoS3b_card_le_of_linearIndependent {τ : Tag} (K : KacData τ)
    (D : Finset (Option (Fin τ.rank))) (l : ℤ) (s : Finset (Fin τ.rank → ℤ))
    (hs : (s : Set (Fin τ.rank → ℤ)) ⊆ partOf K D l)
    (hli : LinearIndependent ℚ (fun v : s => toRat (v : Fin τ.rank → ℤ))) :
    s.card ≤ D.card := by
  let W := levTwoS3b_nodeSpan K D
  have hsub : ∀ x ∈ s, toRat x ∈ W := fun x hx =>
    levTwoS3b_rootsOf_subset_nodeSpan K D x (hs hx).1
  have hliW : LinearIndependent ℚ (fun v : s => (⟨toRat v.1, hsub v.1 v.2⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  have h1 : Fintype.card s ≤ Module.finrank ℚ W :=
    LinearIndependent.fintype_card_le_finrank hliW
  have h2 : Module.finrank ℚ W ≤ D.card := levTwoS3b_finrank_nodeSpan_le K D
  calc s.card = Fintype.card s := (Fintype.card_coe s).symm
    _ ≤ Module.finrank ℚ W := h1
    _ ≤ D.card := h2

theorem levTwoS3b_excRankOK_le_card {τ : Tag} {k n : ℕ} (hk : ExcRankOK τ k) (h : k ≤ n) :
    3 ≤ n ∧ τ.rank ≤ n + 2 ∧ (τ.rank ≤ n + 1 ∨ τ = Tag.E6) := by
  obtain ⟨h3, h2, h1⟩ := hk
  refine ⟨h3.trans h, by omega, ?_⟩
  rcases h1 with h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr h1

end CFSG.StandardType.LevTwo
