module

public import CFSG.Timmesfeld.Transvection.GenerateRel
public import CFSG.Timmesfeld.Transvection.AssembleRel
public import CFSG.Timmesfeld.Transvection.FrameMain
public import CFSG.Timmesfeld.Transvection.Small

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits

@[expose] def ShortRootRegularStatement : Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ → MeetsLines Δ →
    (∀ A ∈ Δ, 4 ≤ Nat.card A) → ∀ A E D E' : Subgroup H, PairFrame Δ A E D E' →
      ∀ C ∈ lineOf Δ A D, C ≠ D → ∃ x ∈ shortRootGroup Δ E A D E', conjSub A x = C

@[expose] def FrameImagesStatement : Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ → MeetsLines Δ →
    ∀ f : ℕ, 2 ≤ f → (∀ A ∈ Δ, Nat.card A = 2 ^ f) →
    ∀ (r : ℕ) (hr : 2 ≤ r) (P Q : Fin r → Subgroup H), IsSmallFrame Δ P Q ⟨r - 1, by omega⟩ →
      (∃ R : SpRelations r (GaloisField 2 f) H, R.HasFrameImages Δ P Q) ∨
      ∃ R : SURelations r (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) H,
        R.HasFrameImages Δ P Q

@[expose] def FrameRelationsStatement : Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ → MeetsLines Δ →
    ∀ f : ℕ, 2 ≤ f → (∀ A ∈ Δ, Nat.card A = 2 ^ f) →
    ∀ (r : ℕ) (hr : 2 ≤ r) (P Q : Fin r → Subgroup H), IsSmallFrame Δ P Q ⟨r - 1, by omega⟩ →
      (∃ R : SpRelations r (GaloisField 2 f) H, R.Generates ∧
        ((Symplectic.rootDatum r (GaloisField 2 f)).rootGroup
          (Pi.single (⟨r - 1, by omega⟩ : Fin r) 1)).map (R.toHom hr) ∈ Δ) ∨
      ∃ R : SURelations r (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) H, R.Generates ∧
        ∃ A ∈ Δ, ∀ g, g ∈ A ↔ ∃ c, unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = c ∧
          R.ξL (Sum.inl ⟨r - 1, by omega⟩) c = g

private theorem four_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem frameRelationsStatement_of (hA4 : ShortRootRegularStatement)
    (h : FrameImagesStatement) : FrameRelationsStatement := by
  intro H _ Δ hyp hml f hf hcard r hr P Q hfr
  have := hyp.finite
  have h4 : ∀ A ∈ Δ, 4 ≤ Nat.card A := fun A hA => (hcard A hA).symm ▸ four_le_two_pow hf
  have hthick := thickLines_of_meetsLines hyp.cls hyp.center hml
  have hreg : ∀ i j : Fin r, i ≠ j → ∀ C ∈ lineOf Δ (P i) (P j), C ≠ P j →
      ∃ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = C :=
    fun i j hij => hA4 H Δ hyp hml h4 _ _ _ _ (hfr.toIsFrame.pairFrame hij)
  rcases h H Δ hyp hml f hf hcard r hr P Q hfr with ⟨R, hR⟩ | ⟨R, hR⟩
  · exact Or.inl ⟨R, hR.generates hyp.cls hyp.points hml hthick (by omega) hfr hreg,
      hR.map_rootGroup_single_last_mem hr (hfr.memP _)⟩
  · exact Or.inr ⟨R, hR.generates hyp.cls hyp.points hml hthick (by omega) hfr hreg,
      hR.exists_long (by omega) (hfr.memP _)⟩

theorem transvectionStatementFrameLarge_of (h : FrameRelationsStatement) :
    TransvectionStatementFrameLarge := by
  intro H _ Δ hyp hml h4 r hr P Q k hfr
  have := hyp.finite
  obtain ⟨f, hf1, hf⟩ := exists_card_eq_two_pow hyp.cls (hfr.memP ⟨0, by omega⟩)
  have hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ f := fun A hA =>
    (hyp.cls.root.card_eq hA (hfr.memP _)).trans hf
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have h2 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := h4 _ (hfr.memP ⟨0, by omega⟩)
    omega
  obtain ⟨P', Q', hfr', -⟩ := hfr.exists_last (by omega)
  rcases h H Δ hyp hml f hf2 hcard r hr P' Q' hfr' with ⟨R, hgen, hlong⟩ | ⟨R, hgen, hlong⟩
  · exact ⟨f, hf1, hcard, (transvectionConclusionRank_of_spRelations hyp.cls.root hf1 hr
      (Or.inl hf2) R hgen hlong).1⟩
  · exact ⟨f, hf1, hcard, (transvectionConclusionRank_of_suRelations hyp.cls.root hf1 hr R hgen
      hyp.center hlong).1⟩

theorem transvectionStatementFrameLarge_of_images (hA4 : ShortRootRegularStatement)
    (h : FrameImagesStatement) : TransvectionStatementFrameLarge :=
  transvectionStatementFrameLarge_of (frameRelationsStatement_of hA4 h)

end CFSG.Timmesfeld.Transvection
