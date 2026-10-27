module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcToral
public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.RankThree.PartOne.KE.F4Regular
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.Steinberg.Adjoint.Perfect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley

namespace LayerExc

theorem exists_subCoreFamily_centralizer_of_conj {L : Type} [Group L] (g : L) (A : Subgroup L)
    (h : ∃ (β : Type) (S : β → Subgroup L), LayerCores.IsSubCoreFamily
      (Subgroup.centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup L) : Set L)) S) :
    ∃ (β : Type) (S : β → Subgroup L),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set L)) S := by
  obtain ⟨β, S, hS⟩ := h
  refine ⟨β, fun c => (S c).comap (MulAut.conj g).toMonoidHom, ?_⟩
  rw [LayerFacts.centralizer_eq_comap_map (MulAut.conj g) A]
  exact hS.comap (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (by
    rw [MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective]
    exact le_top)

theorem exists_subCoreFamily_centralizer_bot {L : Type} [Group L] (hL : CFSG.IsQuasisimple L)
    (hZ : Subgroup.center L = ⊥) :
    ∃ (β : Type) (S : β → Subgroup L),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer ((⊥ : Subgroup L) : Set L)) S := by
  refine ⟨Unit, fun _ => ⊤, ?_⟩
  have hC : Subgroup.centralizer ((⊥ : Subgroup L) : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  rw [hC]
  refine ⟨fun _ => le_rfl, fun _ => IsSubnormal.refl _, fun _ => ?_, ⟨0, ?_⟩, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hL
  · rw [LayerFacts.ggDer_zero]
    exact le_iSup (fun _ : Unit => (⊤ : Subgroup L)) ()
  · intro z _ hz _
    have hzZ : z ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun y => (hz y (Subgroup.mem_iSup_of_mem () trivial)).symm
    rw [hZ, Subgroup.mem_bot] at hzZ
    exact hzZ

end LayerExc

section Split


@[expose] def GGExcSplitCase (τ : Tag) (K : Type) [Field K] (p : ℕ)
    (A : Subgroup ↥(adjointGroup τ K)) : Prop :=
  A = ⊥ ∨ (¬ p ∣ Nat.card (WeylGroup τ) ∧ (∀ x ∈ A, x ^ p = 1) ∧
    ∃ g : ↥(adjointGroup τ K), ∀ x ∈ A,
      ((g * x * g⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K) ∈ torusGroup τ K)

theorem ggExcSplitCase_F4 {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {A : Subgroup ↥(adjointGroup .F4 K)} (hexp : ∀ x ∈ A, x ^ p = 1) (g : ↥(adjointGroup .F4 K))
    (hg : ∀ x ∈ A, ((g * x * g⁻¹ : ↥(adjointGroup .F4 K)) : ModGL .F4 K) ∈ torusGroup .F4 K) :
    GGExcSplitCase .F4 K p A :=
  Or.inr ⟨CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp hp3, hexp, g, hg⟩

theorem ggExcSplitCase_E {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 < p) {A : Subgroup ↥(adjointGroup τ K)} (hexp : ∀ x ∈ A, x ^ p = 1)
    (g : ↥(adjointGroup τ K))
    (hg : ∀ x ∈ A, ((g * x * g⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K) ∈ torusGroup τ K) :
    GGExcSplitCase τ K p A :=
  Or.inr ⟨CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp hp7 (Or.inr hτ), hexp, g, hg⟩

theorem LayerExc.exists_subCoreFamily_of_splitCase {τ : Tag} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hq : CFSG.IsQuasisimple ↥(adjointGroup τ K)) {p : ℕ} (hp : p.Prime)
    (A : Subgroup ↥(adjointGroup τ K)) (hs : GGExcSplitCase τ K p A) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S := by
  rcases hs with rfl | ⟨hord, hexp, g, hg⟩
  · exact LayerExc.exists_subCoreFamily_centralizer_bot hq center_adjointGroup_eq_bot
  · by_cases hA1 : A = ⊥
    · subst hA1
      exact LayerExc.exists_subCoreFamily_centralizer_bot hq center_adjointGroup_eq_bot
    refine LayerExc.exists_subCoreFamily_centralizer_of_conj g A ?_
    refine LayerExc.exists_subCoreFamily_centralizer_of_le_torusGroup hp hord _ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one]
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
      exact hA1

end Split

section Tags

@[expose] def GGExcAdjCoreRestInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ A : Subgroup ↥(adjointGroup τ K), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ¬ GGExcSplitCase τ K p A →
        ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
          LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S

theorem ggExcAdjCoreInput_of_rest {τ : Tag}
    (hq : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], CFSG.IsQuasisimple ↥(adjointGroup τ K))
    (h : GGExcAdjCoreRestInput τ) : GGExcAdjCoreInput τ := by
  intro K _ _ _ p hp hp2 A hA hAc
  by_cases hs : GGExcSplitCase τ K p A
  · exact LayerExc.exists_subCoreFamily_of_splitCase (hq K) hp A hs
  · exact h K p hp hp2 A hA hAc hs

theorem ggLayerTags_F4_of_rest (h : GGExcAdjCoreRestInput .F4) :
    GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4 :=
  ggLayerTags_F4_of_core (ggExcAdjCoreInput_of_rest
    (fun K _ _ _ => CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K) h)

theorem ggLayerTags_E8_of_rest (h : GGExcAdjCoreRestInput .E8) :
    GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8 :=
  ggLayerTags_E8_of_core (ggExcAdjCoreInput_of_rest
    (fun K _ _ _ => CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K) h)

theorem ggLayerTags_E7_of_rest (h : GGExcAdjCoreRestInput .E7) :
    GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7 :=
  ggLayerTags_E7_of_core (ggExcAdjCoreInput_of_rest
    (fun K _ _ _ => CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K)
      (CFSG.LieType.CurtisTits.isQuasisimple_e7 K)) h)

theorem ggLayerInputs_of_exc_rest (hF4 : GGExcAdjCoreRestInput .F4)
    (hE7 : GGExcAdjCoreRestInput .E7) (hE8 : GGExcAdjCoreRestInput .E8)
    (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_remaining_five (ggLayerTags_F4_of_rest hF4) hE6 (ggLayerTags_E7_of_rest hE7)
    (ggLayerTags_E8_of_rest hE8) hTwE6

end Tags

end CFSG.StandardType
