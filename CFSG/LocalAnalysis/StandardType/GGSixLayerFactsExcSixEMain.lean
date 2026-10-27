module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEToral
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcE6
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

namespace LayerSixE

section Inndiag


@[expose] noncomputable def inndiagAut (τ : Tag) (K : Type) [Field K] :
    Subgroup (MulAut ↥(adjointGroup τ K)) :=
  (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range ⊔
    (rootDiagAutHom τ K).range

end Inndiag

section E6


theorem ker_le_ker_e6Isogeny {k : Type} [Field k] [Finite k] {G : Type*} [Group G]
    {ψ : ↥(e6Data_valid.minGroup k) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k)) :
    ψ.ker ≤ (e6Isogeny k).ker :=
  hker.trans CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.ge

theorem exists_induces_E6 {k : Type} [Field k] [Finite k] [CharP k 2] {G : Type*} [Group G]
    (ψ : ↥(e6Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k)) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hc : GGPsiInnerDiag (e6Datum k) ψ c) :
    ∃ α ∈ inndiagAut .E6 k, GGInduces (e6Isogeny k) ψ c α := by
  have hkπ := ker_le_ker_e6Isogeny hker
  obtain ⟨g, ⟨u, rfl⟩, a, ha⟩ := PsiDiagChar.exists_char_E6 ψ hker hc
  have hgN : ψ u ∈ Subgroup.normalizer (ψ.range : Set G) := Subgroup.le_normalizer ⟨u, rfl⟩
  have hdN : (c * ψ u)⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    inv_mem (mul_mem hcN hgN)
  have hδ : GGInduces (e6Isogeny k) ψ (c * ψ u)⁻¹ (rootDiagAutHom .E6 k a) := by
    refine GGInduces.of_generators hkπ (closure_xm_simple_eq_top e6Data_valid k) hdN ?_
    rintro z ⟨i, t, rfl | rfl⟩
    · refine ⟨e6Data_valid.xm k (Pi.single i 1) ((a i : k) * t), ?_, ?_⟩
      · rw [inv_inv, (ha i t).1]
      · rw [RootCentExc.e6Isogeny_xm_single_eq, RootCentExc.e6Isogeny_xm_single_eq,
          RootCentExc.rootDiagAutHom_adjX]
    · refine ⟨e6Data_valid.xm k (-Pi.single i 1) (((a i)⁻¹ : kˣ) * t), ?_, ?_⟩
      · rw [inv_inv, (ha i t).2]
      · rw [RootCentExc.e6Isogeny_xm_neg_single_eq, RootCentExc.e6Isogeny_xm_neg_single_eq,
          RootCentExc.rootDiagAutHom_adjY]
  have hδ' := hδ.inv
  rw [inv_inv] at hδ'
  have hc' := hδ'.mul (Subgroup.le_normalizer ⟨u⁻¹, rfl⟩) (GGInduces.psi hkπ u⁻¹)
  have hce : c * ψ u * ψ u⁻¹ = c := by rw [map_inv, mul_inv_cancel_right]
  rw [hce] at hc'
  refine ⟨_, mul_mem (Subgroup.mem_sup_right (inv_mem ⟨a, rfl⟩))
    (Subgroup.mem_sup_left ⟨_, rfl⟩), hc'⟩

end E6

end LayerSixE

section Tags

@[expose] def GGE6InndiagCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ A : Subgroup (MulAut ↥(adjointGroup .E6 K)), IsPGroup p A →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A ≤ LayerSixE.inndiagAut .E6 K →
        ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .E6 K)),
          LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S

theorem ggLayerTags_E6_of_inndiagCore (h : GGE6InndiagCoreInput) :
    GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm hN hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm hN hdiag => ?_⟩ <;>
  · obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have : Finite ↥(e6Data_valid.minGroup (GaloisField 2 f)) :=
      CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
    have hodd : Odd (Nat.card (e6Isogeny (GaloisField 2 f)).ker) := by
      have h2 := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker
        (GaloisField 2 f) (p := 2)
      exact Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
    have hl := LayerSixE.ggLayer_of_model (e6Isogeny_surjective (GaloisField 2 f))
      (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f))
      hodd (LayerSixE.ker_le_ker_e6Isogeny hker) hE hcomm hN
      (fun e he => LayerSixE.exists_induces_E6 ψ hker (hN he) (hdiag e he))
      (fun A hA hAc hAD => h (GaloisField 2 f) p hp hp2 A hA hAc hAD)
    first
    | exact hl.1
    | exact hl.2

@[expose] def GGE6InndiagCoreNonToralInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ A : Subgroup (MulAut ↥(adjointGroup .E6 K)), IsPGroup p A →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A ≤ LayerSixE.inndiagAut .E6 K →
        ¬ LayerSixE.GGInndiagToral .E6 K A →
          ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .E6 K)),
            LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S

theorem ggE6InndiagCoreInput_of_nonToral (hW : GGWeylFamQuotSolvInput .E6)
    (hN : GGE6InndiagCoreNonToralInput) : GGE6InndiagCoreInput := by
  intro K _ _ _ p hp hp2 A hA hAc hAD
  by_cases ht : LayerSixE.GGInndiagToral .E6 K A
  · exact LayerSixE.exists_subCoreFamily_autFix_of_toral
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K) hW hp hp2 A hA ht
  · exact hN K p hp hp2 A hA hAc hAD ht

theorem ggLayerTags_E6_of_nonToral (hW : GGWeylFamQuotSolvInput .E6)
    (hN : GGE6InndiagCoreNonToralInput) : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6 :=
  ggLayerTags_E6_of_inndiagCore (ggE6InndiagCoreInput_of_nonToral hW hN)

end Tags

end CFSG.StandardType
