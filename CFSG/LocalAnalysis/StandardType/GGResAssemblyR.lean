module

public import CFSG.LocalAnalysis.StandardType.GGResAssembly
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResConfig_of_model_disj
    (hDT : GGResDepTypeInput)
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (h1b : GGResCaseIQFourInput) (h1c : GGResCaseIQTwoInput)
    (h2b : GGResCaseIISmallInput)
    (h4a : GGResDepE6Input) (h4b : GGResE6DepLabelInput)
    (h5a : GGResDepAThreeInput) (h5b : GGResDepAFiveInput)
    (h6a : GGResTwoNodeIndepInput) (h6b : GGResTwoNodeDepInput) (h6c : GGResMaxRankInput)
    (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input) (h6f : GGResSevenInput)
    (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hM : GGResLeviDatum p Bs L J K ggSelAny ggTypAny ∨ GGResRowAt ggRowNonLevi p J L ∨
      GGResRowAt ggRowNonLevi p J K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases hM with hD | hNL | hNK
  · rcases hD.cases with hI | hII | hDep
    · rcases hI.split (ggTypRankGe 8) with hr | hr
      · exact ggResCaseILargeInput_of_inputs hKG hOrb hFix hFixK hJr hPump hLB hSP G p B Bs x L D
          J y K hH hF hS hE (hr.mono (fun _ _ h => h) (fun _ _ h => h.2))
      · have hlt : GGResLeviDatum p Bs L J K ggSelI (ggTypRankLt 8) :=
          hr.mono (fun _ _ h => h) (fun _ _ h => by
            have h2 := h.2
            simp only [ggTypRankGe, ggTypRankLt] at h2 ⊢
            omega)
        by_cases hq : GGInnerDiagOnLabel GGLabQTwo p Bs L
        · exact h1c G p B Bs x L D J y K hH hF hS hE ⟨hlt, hq⟩
        · exact h1b G p B Bs x L D J y K hH hF hS hE ⟨hlt, hq⟩
    · rcases hII.split (ggTypRankGe 9) with hr | hr
      · exact ggResCaseIILargeInput_of_inputs hKG hOrb hFix hFixK G p B Bs x L D J y K hH hF hS hE
          (hr.mono (fun _ _ h => h) (fun _ _ h => h.2))
      · exact h2b G p B Bs x L D J y K hH hF hS hE (hr.mono (fun _ _ h => h) (fun _ _ h => by
          have h2 := h.2
          simp only [ggTypRankGe, ggTypRankLt] at h2 ⊢
          omega))
    · rcases hDT G p B Bs x L D J y K hH hDep with ⟨hp3, hE6⟩ | hA
      · by_cases hsh : GGResE6DepShape p Bs L J K
        · obtain ⟨lab₀, hlab, hmL, hmK⟩ := h4b G p B Bs x L D J y K hH hsh
          obtain ⟨hp3', hcard, hdat⟩ := hsh
          subst hp3'
          exact absurd ⟨rfl, hcard, hdat.dependent (fun _ _ hal hl ha => hl (hal ha)) (by decide),
            lab₀, hlab, hmL, hmK⟩ hE
        · exact h4a G p B Bs x L D J y K hH hF hS hE ⟨hp3, hE6, hsh⟩
      · by_cases hp3 : p = 3
        · exact h5a G p B Bs x L D J y K hH hF hS hE ⟨hp3, hA⟩
        · exact h5b G p B Bs x L D J y K hH hF hS hE ⟨hp3, hA⟩
  · rcases hNL.cases with h | h | h | h | h | h
    · by_cases hx : x ∈ L
      · exact h6a G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨h, hx⟩)
      · exact h6b G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨h, hx⟩)
    · exact h6c G p B Bs x L D J y K hH hF hS hE (Or.inl h)
    · exact h6d G p B Bs x L D J y K hH hF hS hE (Or.inl h)
    · exact h6e G p B Bs x L D J y K hH hF hS hE (Or.inl h)
    · exact h6f G p B Bs x L D J y K hH hF hS hE (Or.inl h)
    · exact h6g G p B Bs x L D J y K hH hF hS hE (Or.inl h)
  · rcases hNK.cases with h | h | h | h | h | h
    · by_cases hy : y ∈ K
      · exact h6a G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨h, hy⟩)
      · exact h6b G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨h, hy⟩)
    · exact h6c G p B Bs x L D J y K hH hF hS hE (Or.inr h)
    · exact h6d G p B Bs x L D J y K hH hF hS hE (Or.inr h)
    · exact h6e G p B Bs x L D J y K hH hF hS hE (Or.inr h)
    · exact h6f G p B Bs x L D J y K hH hF hS hE (Or.inr h)
    · exact h6g G p B Bs x L D J y K hH hF hS hE (Or.inr h)

private theorem l05nAR_twoNode_le_nonLevi {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowTwoNode p J X) : GGResRowAt ggRowNonLevi p J X := by
  obtain ⟨a, c, ha, hc, hJ, hX, hr⟩ := h
  exact ⟨a, c, ha, hc, hJ, hX, Or.inl hr⟩

theorem ggCoxeterLabelResidualOffE6DepInput_of_leaves_multi
    (hM : GGResModelInputR) (hDT : GGResDepTypeInput)
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (h1b : GGResCaseIQFourInput) (h1c : GGResCaseIQTwoInput)
    (h2b : GGResCaseIISmallInput)
    (h4a : GGResDepE6Input) (h4b : GGResE6DepLabelInput)
    (h5a : GGResDepAThreeInput) (h5b : GGResDepAFiveInput)
    (h6a : GGResTwoNodeIndepInput) (h6b : GGResTwoNodeDepInput) (h6c : GGResMaxRankInput)
    (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input) (h6f : GGResSevenInput)
    (h6g : GGResTwA2Input) (h7 : GGResCorank2CInput ∧ GGResSUCorank2Input ∧
        GGResMultiNodeRestInput) : GGCoxeterLabelResidualOffE6DepInput := by
  refine ggCoxeterLabelResidualOffE6DepInput_of_leaf ?_
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE _
  have hMulti : (GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumLE3 p Bs K J L ggSelAny ggTypAny) →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    intro hP
    by_cases h2 : GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K
    · rcases h2 with h2 | h2
      · exact ggResConfig_of_model_disj hDT hKG hOrb hFix hFixK hJr hPump hLB hSP h1b h1c h2b h4a
          h4b h5a h5b h6a h6b h6c h6d h6e h6f h6g hH hF hS hE
          (Or.inr (Or.inl (l05nAR_twoNode_le_nonLevi h2)))
      · exact ggResConfig_of_model_disj hDT hKG hOrb hFix hFixK hJr hPump hLB hSP h1b h1c h2b h4a
          h4b h5a h5b h6a h6b h6c h6d h6e h6f h6g hH hF hS hE
          (Or.inr (Or.inr (l05nAR_twoNode_le_nonLevi h2)))
    · by_cases hC : GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K
      · exact h7.1 G p B Bs x L D J y K hH hF hS hE hC
      · by_cases hSU : GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K
        · exact h7.2.1 G p B Bs x L D J y K hH hF hS hE hSU
        · exact h7.2.2 G p B Bs x L D J y K hH hF hS hE ⟨hP, h2, hC, hSU⟩
  rcases hM G p B Bs x L D J y K hH with hD | hMN | hMK | hNL | hNK
  · exact ggResConfig_of_model_disj hDT hKG hOrb hFix hFixK hJr hPump hLB hSP h1b h1c h2b h4a h4b
      h5a h5b h6a h6b h6c h6d h6e h6f h6g hH hF hS hE (Or.inl hD)
  · exact hMulti (Or.inl hMN)
  · exact hMulti (Or.inr hMK)
  · exact ggResConfig_of_model_disj hDT hKG hOrb hFix hFixK hJr hPump hLB hSP h1b h1c h2b h4a h4b
      h5a h5b h6a h6b h6c h6d h6e h6f h6g hH hF hS hE (Or.inr (Or.inl hNL))
  · exact ggResConfig_of_model_disj hDT hKG hOrb hFix hFixK hJr hPump hLB hSP h1b h1c h2b h4a h4b
      h5a h5b h6a h6b h6c h6d h6e h6f h6g hH hF hS hE (Or.inr (Or.inr hNK))

end CFSG.StandardType

end
