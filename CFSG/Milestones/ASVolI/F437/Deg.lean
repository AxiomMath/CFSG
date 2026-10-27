module

import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F437.Main
public import CFSG.Milestones.ASVolI.F437.Odd
public import CFSG.Milestones.ASVolI.F437.Quot

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF437_ClassInputDeg (κ : GLKind) (degree : ℕ) : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (hyp : HypF_4_4 κ 2 degree Gp M₁ M₂),
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) →
    ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
      hyp.toHypF_4_4g.chart.IsFieldInv t ∨
        (hyp.toHypF_4_4g.chart.IsGraphInv t ∧ IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 degree ∧
          hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal t) ∨
        hyp.toHypF_4_4g.chart.IsTypeIIIInv t

@[expose] def burnsideF437_FixedInputDeg (κ : GLKind) (degree : ℕ) : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 degree Gp M₁ M₂) (fb : E), burnsideF437_Inv Gp M₁ M₂ fb →
    (hyp.toHypF_4_4g.chart.IsFieldInv fb ∨ hyp.toHypF_4_4g.chart.IsGraphInv fb) →
      burnsideF437_FixedFacts κ degree Gp M₁ M₂ hyp.toHypF_4_4g.chart fb

@[expose] def burnsideF437_SylowInputDeg (κ : GLKind) (degree : ℕ) : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y) (M : Type) [Group M]
    (ε : Y →* M) (z : M) (hyp : HypF_4_31 κ degree Gp M₁ M₂ β ε z),
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb →
      (fb : E) ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → (fb : E) * (fb : E) = 1 →
      (hyp.amalgam.toHypF_4_4g.chart.IsFieldInv (fb : E) ∨
        hyp.amalgam.toHypF_4_4g.chart.IsGraphInv (fb : E)) →
      ChF.IsSylowOf 2
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
        (cenIn Gp (fb : E)) →
      (ChF.IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
          (Subgroup.centralizer ({bM β ε fb} : Set M)) ∨
        (κ = .U4 ∧ degree = 1 ∧ Nonempty (E ≃* MulAut Gp) ∧
          Nonempty (E ≃* β.G0) ∧ IsL43 M))

@[expose] def burnsideF437_SylowInputDegIII (κ : GLKind) (degree : ℕ) : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y) (M : Type) [Group M]
    (ε : Y →* M) (z : M) (hyp : HypF_4_31 κ degree Gp M₁ M₂ β ε z),
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb →
      (fb : E) ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → (fb : E) * (fb : E) = 1 →
      (hyp.amalgam.toHypF_4_4g.chart.IsFieldInv (fb : E) ∨
        hyp.amalgam.toHypF_4_4g.chart.IsGraphInv (fb : E)) →
      ¬ hyp.amalgam.toHypF_4_4g.chart.IsTypeIIIInv (fb : E) →
      ChF.IsSylowOf 2
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
        (cenIn Gp (fb : E)) →
      (ChF.IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
          (Subgroup.centralizer ({bM β ε fb} : Set M)) ∨
        (κ = .U4 ∧ degree = 1 ∧ Nonempty (E ≃* MulAut Gp) ∧
          Nonempty (E ≃* β.G0) ∧ IsL43 M))

theorem burnsideF437_sylowInputDegIII_of {κ : GLKind} {degree : ℕ}
    (h : burnsideF437_SylowInputDeg κ degree) : burnsideF437_SylowInputDegIII κ degree :=
  fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp Tb hTb fb hfbT hfbS hsq hFG _ hsyl =>
    h E Gp M₁ M₂ Y β M ε z hyp Tb hTb fb hfbT hfbS hsq hFG hsyl

theorem burnsideF437_classInputDeg_of_F_4_29 (h : F_4_29) (κ : GLKind) (degree : ℕ)
    (hκ : κ.IsLie) : burnsideF437_ClassInputDeg κ degree :=
  fun E _ Gp M₁ M₂ hyp => burnsideF437_classInput_of_F_4_29 h κ degree E Gp M₁ M₂ hyp hκ

theorem burnsideF437_F437KindDeg_ofIII (hcompat : NativeChartCompatibilityGoal) {κ : GLKind}
    {degree : ℕ} (hcls : burnsideF437_ClassInputDeg κ degree)
    (hfix : burnsideF437_FixedInputDeg κ degree) (h4 : burnsideF437_SylowInputDegIII κ degree) :
    burnsideF437_F437KindDeg κ degree := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp chart Tb hTb fb hfbT hfbS hsq hiii hsyl
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hfG : (fb : E) ∉ Gp := burnsideF437_not_mem_Gp hsyl (fun h => hfbS h.1) hsq
  have hf1 : (fb : E) ≠ 1 := burnsideF437_ne_one hfbS
  have hcls' := hcls E Gp M₁ M₂ hyp.amalgam Tb hTb fb hfbT hfbS hsq
  have hFG : chart.IsFieldInv (fb : E) ∨ chart.IsGraphInv (fb : E) := by
    rcases hcls' with h | h | h
    · exact Or.inl h
    · exact Or.inr h.1
    · exact absurd h hiii
  have hinv : burnsideF437_Inv Gp M₁ M₂ (fb : E) := ⟨fb.2, hfG, hsq, hsyl⟩
  have F := hfix E Gp M₁ M₂ hyp.amalgam fb hinv hFG
  have hP := burnsideF4j_parabolics hcompat hyp.amalgam
  obtain ⟨hSyl, hB⟩ := burnsideF437_sylow_sbar hP
  have hRN := burnsideF437_normalizer_le_of_unique hyp.amalgam.split hB hSyl inf_le_left
    F.unique_sylow
  have hfrat := burnsideF437_frattini hsyl hRN
  have hdyn := burnsideF437_dynkin hsyl hRN
  have hrig : Subgroup.centralizer ((f437Dbar Gp (fb : E) : Subgroup E) : Set E) ⊓
      f437Ebar (fb : E) = Subgroup.zpowers (fb : E) :=
    le_antisymm F.rigid burnsideF437_zpowers_le
  have hpar : IsLieParabolics 2 (f437Dbar Gp (fb : E)) (cenIn (Gp ⊓ (M₁ ⊓ M₂)) (fb : E))
      (f437DbarOne Gp M₁ (fb : E)) (f437DbarTwo Gp M₂ (fb : E)) := F.parabolics
  have hQ : ∀ {kind : GLKind} {d : ℕ}, IsGenLie (f437Dbar Gp (fb : E)) kind 2 d →
      F437QuotientAssembly Gp M₁ M₂ (fb : E) kind d := fun hlie =>
    burnsideF437_quotientAssembly fb.2 hfG hf1 hsq hlie hpar F.rigid hfrat hdyn
  refine ⟨hFG, ?_, ⟨burnsideF437_sup_eq hpar, burnsideF437_inf_eq, hpar,
    burnsideF437_restriction_exists β hyp.faithful Gp (fb : E)⟩,
    burnsideF437_inter_map β hyp.faithful Gp (fb : E),
    ⟨burnsideF437_conj_mem, hrig, hfrat, hdyn⟩, ?_⟩
  · rcases hFG with hfield | hgraph
    · left
      obtain ⟨-, -, sd, hsd, hdeg, -⟩ := id hfield
      have hd2 : degree / 2 = sd := by omega
      have hlie : IsGenLie (f437Dbar Gp (fb : E)) κ 2 sd := hd2 ▸ F.field_lie hfield
      exact ⟨sd, hsd, hdeg, hfield, hlie, hQ hlie⟩
    · right
      have hdata : IsGenLie (f437Dbar Gp (fb : E)) .Sp4 2 degree ∧
          chart.GraphFixedMarkingGoal (fb : E) := by
        rcases hcls' with h | h | h
        · exfalso
          obtain ⟨h4', h5'⟩ := burnsideF437_field_kind h
          rcases burnsideF437_graph_kind hgraph with h' | h'
          · exact h4' h'
          · exact h5' h'
        · exact h.2
        · exact absurd h hiii
      exact ⟨hgraph, burnsideF437_graph_kind hgraph, hdata.1, hdata.2, hQ hdata.1⟩
  · exact h4 E Gp M₁ M₂ Y β M ε z hyp Tb hTb fb hfbT hfbS hsq hFG hiii hsyl

theorem burnsideF437_F437KindDeg_of (hcompat : NativeChartCompatibilityGoal) {κ : GLKind}
    {degree : ℕ} (hcls : burnsideF437_ClassInputDeg κ degree)
    (hfix : burnsideF437_FixedInputDeg κ degree) (h4 : burnsideF437_SylowInputDeg κ degree) :
    burnsideF437_F437KindDeg κ degree :=
  burnsideF437_F437KindDeg_ofIII hcompat hcls hfix (burnsideF437_sylowInputDegIII_of h4)

end CFSG.ASVolI
