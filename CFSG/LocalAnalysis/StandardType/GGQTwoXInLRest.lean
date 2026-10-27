module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCommonMain
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverSmall
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeExc
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcInsideMoved
public import CFSG.LocalAnalysis.StandardType.GGExcGen
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.StandardType.GGQ2InLCommonMainBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

theorem ggQTwoXInL_ambOn_legacy {c : LargeEvenLieTag → Prop} {G : Type} [Group G]
    {Bs X : Subgroup G} (h : GGQTwoXInLAmbOn c Bs X) :
    LargeEvenMarking ↥X (fun lab _ _ _ _ _ => c lab.tag) := by
  obtain ⟨hX, lab, hlab, hraw⟩ :=
    Canonical.largeEvenMarking_mono (P' := fun lab _ _ _ _ _ => c lab.tag)
      (fun _ _ _ _ _ _ h => h.1) h
  exact ⟨hX, lab, hlab,
    LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenRawDatumLegacy_of_canonical_carrier
      (T := fun R _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ _ : ↥X ⧸ Subgroup.center ↥X ≃* R, c lab.tag) hraw⟩

theorem classicalCatalogue_ambientLabel (k : FrameKind) :
    ClassicalLabel (classicalCatalogue k).ambientLabel := by
  cases k with
  | lin t ε => exact Or.inl rfl
  | symp t => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | orth t δ =>
    change ClassicalLabel (planeAmbientLabel (.orthogonal δ) t)
    by_cases h : Even t <;> simp [planeAmbientLabel, ClassicalLabel, h]
  | unitFull N => exact Or.inr (Or.inl rfl)
  | unitHeart N => exact Or.inr (Or.inl rfl)
  | exceptional m => exact Or.inl rfl

theorem not_actualFrame_classicalCatalogue (hrig : GGLabelRigidInput) {G : Type} [Group G]
    {H Bs : Subgroup G} (hm : LargeEvenMarking ↥H (fun lab _ _ _ _ _ => ExceptionalLabel lab))
    (k : FrameKind) : ¬ ActualFrame H Bs (classicalCatalogue k) := by
  rintro ⟨real⟩
  obtain ⟨labA, hlA, hasA, _, _, _, _, _, hA⟩ := largeEvenMarking_exists_hasLabel real.innerDiag
  obtain ⟨labX, hlX, hasX, -, -, -, -, -, hX⟩ := largeEvenMarking_exists_hasLabel hm
  have hX' : ExceptionalLabel labX := hX
  have heq : labA = labX := excg_labelIso_eq_of_exc (hrig labA labX _ hlA hlX hasA hasX) (by
    rcases hX' with h | h | h | h | h <;> simp [h])
  have hcl : ClassicalLabel labA := by
    rw [show labA = _ from hA.1]
    exact classicalCatalogue_ambientLabel k
  rw [heq] at hcl
  rcases hX' with h | h | h | h | h <;> simp [ClassicalLabel, h] at hcl

theorem ggQTwoXInLNbrRest_of_placement
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hplEx : PlacementInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue)) :
    GGQTwoXInLNbrRest := by
  intro G _ _ p B Bs x L D J hS hI1 hxL hAmb _
  have hp := ggQ2_pThree hS
  subst hp
  have hc : ∀ t : LargeEvenLieTag, ¬ GGQTwoXInLClTag t →
      (t = .F4 ∨ t = .E6 ∨ t = .twE6 ∨ t = .E7 ∨ t = .E8) ∨
      (t = .G2 ∨ t = .triD4 ∨ t = .twB2 ∨ t = .twF4 ∨ t = .B2der ∨ t = .G2der ∨
        t = .twF4der) ∨
      (t = .G2 ∨ t = .triD4 ∨ t = .twB2 ∨ t = .twF4 ∨ t = .B2der ∨ t = .G2der ∨
        t = .twF4der) := by
    intro t ht
    cases t <;> simp_all [GGQTwoXInLClTag]
  rcases ggQTwoXInL_ambOn_cases hc hAmb with hEx | hSm | hSm
  · have hm := ggQTwoXInL_ambOn_legacy hEx
    obtain ⟨kind, hF⟩ := hplEx hS rfl hm
    by_cases hk : IsClassical kind
    · rw [catalogueOf_classical _ _ hk] at hF
      exact (not_actualFrame_classicalCatalogue ggLabelRigidInput_holds hm kind hF).elim
    · rw [catalogueOf_exceptional _ _ hk] at hF
      cases kind with
      | exceptional m =>
        have hC : InLCommonCases (excRaw m) := by
          by_cases hm4 : m = 4
          · subst hm4
            exact ExcRaw.inLCommonCases_excRaw_four
          · exact inLCommonCases_excRaw m hm4
        exact xInLNbrAtFrame_of_commonCases hLB hP ggLabelRigidInput_holds
          (ExcRaw.rawInsideMoved_excRaw m) hC hS rfl hI1 hxL hF
      | _ => exact (hk trivial).elim
  all_goals exact (ggG0_not_marking_small hS.1 (ggQTwoXInL_ambOn_legacy hSm)).elim

end CFSG.StandardType

end
