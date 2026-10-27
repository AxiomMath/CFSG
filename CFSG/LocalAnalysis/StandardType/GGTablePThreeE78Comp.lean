module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE78Lang
public import CFSG.LocalAnalysis.StandardType.GGTorsionDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE78Cat
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Bridge
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
import CFSG.LocalAnalysis.ComponentClassification.ONanTauCetiPartitionEven

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGCompE78 {X : Type} [Group X] (δ : MulAut X) (J : Subgroup X) : Prop :=
  (∃ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup δ) ∧ J' ≠ J) ∨
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
      TablePThreeKG.E78CompLabel lab

private theorem e78_markChar_eq_two {lab : LargeEvenLabel} (h : lab.tag = .E7 ∨ lab.tag = .E8) :
    markChar lab = 2 := by
  rcases h with h | h <;> simp [markChar, h]

private theorem e78_markDeg_eq {lab : LargeEvenLabel} (h : lab.tag = .E7 ∨ lab.tag = .E8) :
    markDeg lab = lab.n := by
  rcases h with h | h <;> simp [markDeg, h]

private theorem e78_markTag_eq {lab : LargeEvenLabel} (h : lab.tag = .E7 ∨ lab.tag = .E8) :
    markTag lab = .E7 ∨ markTag lab = .E8 := by
  rcases h with h | h <;> simp [markTag, h]

private theorem e78_markTag_mem_chevalleyExceptional {lab : LargeEvenLabel}
    (h : lab.tag = .E7 ∨ lab.tag = .E8) :
    markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
  rcases h with h | h <;> simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, h]

private theorem e78_index_facts {d : TauCeti.LieTypeIndex} {n : ℕ}
    (h : CFSG.Models.NamesTag d .E7 2 n ∨ CFSG.Models.NamesTag d .E8 2 n) :
    ((∃ q : TauCeti.PrimePower, d = .E7 q) ∨ ∃ q : TauCeti.PrimePower, d = .E8 q) ∧
      d.characteristic = 2 := by
  rcases h with h | h <;> cases d <;>
    simp_all [CFSG.Models.NamesTag, TauCeti.LieTypeIndex.characteristic_E7,
      TauCeti.LieTypeIndex.characteristic_E8]

private theorem compE78At_of_mulEquiv {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : CompE78At S) : CompE78At S' := by
  intro b hbmem hb3 hb1 K' hK'
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hα3 : α ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hb3
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup b).map
      (e.symm : S' →* S) = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hfix' : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map
      (e : S →* S') = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup b := by
    rw [← hfix, Subgroup.map_map]
    simp
  have hKcomp : CFSG.Open.IsComponentOf K
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  rcases h α hαmem hα3 hα1 K hKcomp with ⟨K'', hK''c, hK''ne⟩ | ⟨lab, hlab, hlabel, hE78⟩
  · refine Or.inl ⟨K''.map (e : S →* S'), ?_, ?_⟩
    · have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK''c
      rwa [hfix'] at this
    · intro hEq
      apply hK''ne
      have h1 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K'' := by
        rw [Subgroup.map_map]; simp
      have h2 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K := by
        rw [hEq, hK]
      exact h1.symm.trans h2
  · refine Or.inr ⟨lab, hlab, ?_, hE78⟩
    have hKmap : K.map (e : S →* S') = K' := by
      rw [hK, Subgroup.map_map]; simp
    let ε : ↥K ≃* ↥K' :=
      (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
    exact largeEvenRawDatum_mono
      (fun R' _ _ _ ⟨e'⟩ =>
        ⟨(QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).symm.trans e'⟩) hlabel

private theorem e78_inndiagComm_labelAll
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .E7 ∨ lab.tag = .E8) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  rcases h with h | h
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, h])
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, h])

theorem ggTorsion_e78_comp
    {X : Type} [Group X] [Finite X] {δ : MulAut X} {J : Subgroup X}
    (hdat : GGTorsionDatum (fun lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 δ J) : GGCompE78 δ J := by
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .E7 ∨ lab.tag = .E8 := by
    obtain ⟨_, _, _, _, _, _, _, hP0, -⟩ := largeEvenRawDatum_exists hraw
    exact hP0
  have hrawMM : LargeEvenRawDatum lab
      (fun R _ I _ => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, (lab.tag = .E7 ∨ lab.tag = .E8) ∧
          ggInducedAut θ δ ∈ I) ∧ MarkedModel lab R) :=
    largeEvenRawDatum_markedModel hlab
      (fun _ _ _ _ ⟨_, hna, _, _, _⟩ => hna) hraw
  have hraw' := (e78_inndiagComm_labelAll hlab htag) _ hrawMM
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, _hP, hδI⟩, hm⟩, hGuard⟩ :=
    largeEvenRawDatum_exists hraw'
  have hEq : GGInndiagCommEq R I F := hGuard hs hna
  let δbar : MulAut R := ggInducedAut θ δ
  have hδbar1 : δbar ≠ 1 := by
    intro h
    apply hδ1
    exact ggInducedAut_injective_of_perfect hXc θ (h.trans (map_one _).symm)
  have hδbar3 : δbar ^ 3 = 1 := by
    dsimp [δbar]
    rw [← map_pow, hδp, map_one]
  have hβ : δbar ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R := by
    have hmem : δbar ∈ ggInndiag R I := Subgroup.mem_sup_right (Subgroup.subset_closure hδI)
    have hmem2 : δbar ∈ ggInndiagComm R := by rw [← hEq]; exact hmem
    rwa [ggInndiagComm_eq_innAutDerived] at hmem2
  let Jbar : Subgroup R :=
    J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X)))
  have hJbar : IsComponentOf Jbar (ggAutFixedSubgroup δbar) := by
    dsimp [Jbar, δbar]
    exact ggTorsion_isComponentOf_image θ hcomp
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar =
      ggAutFixedSubgroup δbar := Subgroup.ext fun _ => Iff.rfl
  have hC : CFSG.Open.IsComponentOf Jbar
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar) := by
    rw [hfix]
    exact isComponentOf_iff_open.mp hJbar
  have hm0 : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) (markChar lab)
      (markDeg lab) := hm
  have ht : markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags :=
    e78_markTag_mem_chevalleyExceptional htag
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n := by
    have h := hm0.chevalleyExceptionalModel ht
    rwa [e78_markChar_eq_two htag, e78_markDeg_eq htag] at h
  obtain ⟨d, hdnames, ⟨e⟩⟩ := CFSG.TauCetiBridge.exists_index_of_chevalley_even ht hchev
  have hdnames' : CFSG.Models.NamesTag d.1 .E7 2 lab.n ∨
      CFSG.Models.NamesTag d.1 .E8 2 lab.n := by
    rcases e78_markTag_eq htag with hm | hm
    · exact Or.inl (hm ▸ hdnames)
    · exact Or.inr (hm ▸ hdnames)
  obtain ⟨hdE78, hch⟩ := e78_index_facts hdnames'
  have hIcomp : CompE78At (TauCeti.CFSGIndex.lie d).Group :=
    compE78_cat_of_lang d hch hdE78
  have hIcomp' : CompE78At R := compE78At_of_mulEquiv e.symm hIcomp
  rcases hIcomp' δbar hβ hδbar3 hδbar1 Jbar hC with ⟨K', hK', hK'ne⟩ | ⟨lab', hlab', hlabel', hE78'⟩
  · have hK'Ass : IsComponentOf K' (ggAutFixedSubgroup δbar) := by
      rw [← hfix]
      exact isComponentOf_iff_open.mpr hK'
    obtain ⟨J', hJ', hJ'map⟩ :=
      CFSG.StandardType.TablePThreeKG.exists_component_of_induced hXc θ δ hK'Ass
    refine Or.inl ⟨J', hJ', ?_⟩
    intro hJJ'
    apply hK'ne
    have hK'eq : K' = Jbar := by
      rw [← hJ'map, hJJ']
      rfl
    exact hK'eq
  · refine Or.inr ⟨lab', hlab', ?_, hE78'⟩
    obtain ⟨eJ⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
    exact largeEvenRawDatum_mono (fun R' _ _ _ ⟨e'⟩ => ⟨eJ.trans e'⟩) hlabel'

end CFSG.StandardType

end
