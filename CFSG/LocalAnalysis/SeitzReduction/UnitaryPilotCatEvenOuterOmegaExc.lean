module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (EvenOuterFamilyExcInput)
open CFSG.SeitzReduction.LinearPilot (OmegaOuterFixed omega_family_fixed_exact)

theorem false_of_omegaOuterFixed_su {m : ℕ} (hdet : SUmEvenTypeDetAt m) (hm : 4 ≤ m) {X : Type}
    [Group X] [Finite X] {g : ℕ} (h : OmegaOuterFixed X g) {D : Subgroup X} (hD : IsComponent D)
    {f : ℕ} (hDm : LieModel (D ⧸ center D) .PSU m 2 f) : False := by
  rcases h with h | h
  · exact false_of_spFixedOrNoPComponent_su hdet hm h hD hDm
  · obtain ⟨t, n, f', ht, hadm, hmD⟩ :=
      h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)
    obtain ⟨rfl, -, -⟩ := sumTypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_POmega ht hmD) hDm hadm hmD
    rcases ht with h | h <;> exact absurd h (by decide)

theorem catSUmEvenOuterFamilyAt_POmegaPlus {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) :
    CatSUmEvenOuterFamilyAt .POmegaPlus m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  exact (false_of_omegaOuterFixed_su hdet hm
    (omega_family_fixed_exact (Or.inl rfl) hadm hmS σ hσ hout) hD hDm).elim

theorem catSUmEvenOuterFamilyAt_POmegaMinus {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) :
    CatSUmEvenOuterFamilyAt .POmegaMinus m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  exact (false_of_omegaOuterFixed_su hdet hm
    (omega_family_fixed_exact (Or.inr rfl) hadm hmS σ hσ hout) hD hDm).elim

theorem no_sum_component_of_excInput {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m)
    {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ) {S : Type} [Group S] [Finite S]
    {n e : ℕ} (hadm : StatedLieAdmissible τ n 2 e) (hmS : LieModel S τ n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) : False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S n e hadm hmS σ hσ hout D hP
  have hZ : Open.fusionZStar D = center D :=
    ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hD.1
      (ComponentClassification.CatLeaf.pPrimeCore_ne_top_of_isPComponent hP)
  let E : D ⧸ Open.fusionZStar D ≃* D ⧸ center D := QuotientGroup.quotientMulEquivOfEq hZ
  rcases hX with ⟨τ', e', hτ', hadm', hm'⟩ | hU
  · obtain ⟨rfl, -, -⟩ :=
      hdet (D ⧸ center D) f τ' 0 e' hDm hadm' (LieType.CurtisTits.lieModel_of_mulEquiv E hm')
    exact hτ' (by decide)
  · have h1 := GH74.card_of_lieModel_PSU (by norm_num) (by norm_num)
      (LieType.CurtisTits.lieModel_of_mulEquiv E hU)
    rw [show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide] at h1
    have h64 := two_pow_six_dvd_card_of_lieModel_PSU hm hDm
    rw [h1] at h64
    exact absurd h64 (by decide)

theorem catSUmEvenOuterFamilyAt_of_excInput {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ)
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt τ m :=
  fun _ _ _ _ _ _ _ hadm hmS _ hσ hout _ _ hD hDm _ =>
    (no_sum_component_of_excInput hm hdet h hadm hmS hσ hout hD hDm).elim

theorem catSUmEvenOuterFamilyAt_G2
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .G2 m :=
  catSUmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_G2 hm hdet

theorem catSUmEvenOuterFamilyAt_F4
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .F4 m :=
  catSUmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_F4 hm hdet

theorem catSUmEvenOuterFamilyAt_E6
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .E6 m :=
  catSUmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_E6 hm hdet

theorem catSUmEvenOuterFamilyAt_twistedE6
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .twistedE6 m :=
  catSUmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_twistedE6 hm hdet

theorem catSUmEvenOuterFamilyAt_trialityD4
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .trialityD4 m :=
  catSUmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_trialityD4 hm hdet

theorem catSUmEvenOuterFamilyAt_E7
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .E7 m :=
  catSUmEvenOuterFamilyAt_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inl rfl)) hm hdet

theorem catSUmEvenOuterFamilyAt_E8
    {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .E8 m :=
  catSUmEvenOuterFamilyAt_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inr rfl)) hm hdet

end CFSG.SeitzReduction.UnitaryPilot
