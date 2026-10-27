module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4Cat
public import CFSG.LocalAnalysis.StandardType.GGTorsionDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Bridge
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
import CFSG.LocalAnalysis.ComponentClassification.ONanTauCetiPartitionEven

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.LangRat

@[expose] def GGCompF4BC {X : Type} [Group X] (δ : MulAut X) (J : Subgroup X) (n : ℕ) : Prop :=
  (∃ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup δ) ∧ J' ≠ J) ∨
    GGHasLabel ⟨.C, 3, n⟩ (↥J ⧸ Subgroup.center ↥J)

private theorem f4_markChar_eq_two {lab : LargeEvenLabel} (h : lab.tag = .F4) :
    markChar lab = 2 := by
  simp [markChar, h]

private theorem f4_markDeg_eq {lab : LargeEvenLabel} (h : lab.tag = .F4) :
    markDeg lab = lab.n := by
  simp [markDeg, h]

private theorem f4_namesTag_eq_F4 {d : TauCeti.LieTypeIndex} {n : ℕ}
    (h : CFSG.Models.NamesTag d .F4 2 n) : ∃ q : TauCeti.PrimePower, d = .F4 q := by
  cases d <;> simp_all [CFSG.Models.NamesTag]

private theorem f4_index_facts {d : TauCeti.LieTypeIndex} {n : ℕ}
    (h : CFSG.Models.NamesTag d .F4 2 n) :
    (∃ q : TauCeti.PrimePower, d = .F4 q) ∧ d.characteristic = 2 ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d = 2 ^ n := by
  obtain ⟨q, rfl⟩ := f4_namesTag_eq_F4 h
  have hq : q.p = 2 ∧ q.exponent = n := by simpa [CFSG.Models.NamesTag] using h
  refine ⟨⟨q, rfl⟩, ?_, ?_⟩
  · rw [TauCeti.LieTypeIndex.characteristic_F4]
    exact hq.1
  · rw [show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize (TauCeti.LieTypeIndex.F4 q) =
        q.card from rfl, TauCeti.PrimePower.card_def, hq.1, hq.2]

private theorem compF4BCAt_of_mulEquiv {d : TauCeti.LieTypeIndex} {S S' : Type} [Group S]
    [Group S'] (e : S ≃* S') (h : CompF4BCAt d S) : CompF4BCAt d S' := by
  intro β hβmem hβ3 hβ1 K' hK'
  set α : MulAut S := MulAut.congr e.symm β with hα
  have hconj : MulAut.congr e α = β := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e, hconj]
    exact hβmem
  have hα3 : α ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hβ3
  have hα1 : α ≠ 1 := by
    intro h1
    apply hβ1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β).map
      (e.symm : S' →* S) = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hKcomp : CFSG.Open.IsComponentOf K
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  have hfix' : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map (e : S →* S') =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := by
    rw [← hfix, Subgroup.map_map]
    simp
  rcases h α hαmem hα3 hα1 K hKcomp with ⟨K₀, hK₀, hK₀ne⟩ | ⟨F, hF, hFfin, hFcard, ⟨eK⟩⟩
  · refine Or.inl ⟨K₀.map (e : S →* S'), ?_, ?_⟩
    · have hcomp := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK₀
      rwa [hfix'] at hcomp
    · intro heq
      apply hK₀ne
      have hmaps : K₀.map (e : S →* S') = K.map (e : S →* S') := by
        rw [heq, hKmap]
      exact Subgroup.map_injective e.injective hmaps
  · refine Or.inr ⟨F, hF, hFfin, hFcard, ?_⟩
    let ε : ↥K ≃* ↥K' :=
      (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
    exact ⟨(QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).symm.trans eK⟩

private theorem f4_inndiagComm_labelAll
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .F4) :
    LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => ggInndiag R I = ggInndiagComm R) := by
  have htits : lab.tag ≠ .twF4der := by simp [h]
  have hD4 : ¬ (lab.tag = .D ∧ lab.rank = 4) := by simp [h]
  exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenLabelAll_inndiagComm_charTwo
    hlab (f4_markChar_eq_two h) htits hD4

theorem ggTorsion_f4_comp
    {X : Type} [Group X] [Finite X] {δ : MulAut X} {J : Subgroup X}
    (hdat : GGTorsionDatum (fun lab => lab.tag = .F4) 3 δ J) :
    LargeEvenMarking X fun lab _ _ _ _ _ => lab.tag = .F4 ∧ GGCompF4BC δ J lab.n := by
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .F4 := by
    obtain ⟨_, _, _, _, _, _, _, hP0, -⟩ := largeEvenRawDatum_exists hraw
    exact hP0
  have hrawMM : LargeEvenRawDatum lab
      (fun R _ I _ => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, lab.tag = .F4 ∧ ggInducedAut θ δ ∈ I) ∧
        MarkedModel lab R) :=
    largeEvenRawDatum_markedModel hlab
      (fun _ _ _ _ ⟨_, hna, _, _, _⟩ => hna) hraw
  have hraw' := (f4_inndiagComm_labelAll hlab htag) _ hrawMM
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, _hP, hδI⟩, hm⟩, hGuard⟩ :=
    largeEvenRawDatum_exists hraw'
  have hEq : ggInndiag R I = ggInndiagComm R := hGuard hs hna
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
  have htagMark : markTag lab = .F4 := by simp [markTag, htag]
  have ht : markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
    simp [htagMark, CFSG.Blueprint.chevalleyExceptionalTags]
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n := by
    have h := hm0.chevalleyExceptionalModel ht
    rwa [f4_markChar_eq_two htag, f4_markDeg_eq htag] at h
  obtain ⟨d, hdnames, ⟨e⟩⟩ := CFSG.TauCetiBridge.exists_index_of_chevalley_even ht hchev
  rw [htagMark] at hdnames
  obtain ⟨hdF4, hch, hk⟩ := f4_index_facts hdnames
  have hIcomp : CompF4BCAt d.1 (TauCeti.CFSGIndex.lie d).Group :=
    compF4BC_cat_of_lang d hch hdF4
  have hIcomp' : CompF4BCAt d.1 R := compF4BCAt_of_mulEquiv e.symm hIcomp
  have hmain : GGCompF4BC δ J lab.n := by
    rcases hIcomp' δbar hβ hδbar3 hδbar1 Jbar hC with
      ⟨K', hK', hK'ne⟩ | ⟨F', hF', hF'fin, hF'card, ⟨eK'⟩⟩
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
    · refine Or.inr ?_
      obtain ⟨eJ⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
      have hF'card' : Nat.card F' = 2 ^ lab.n := by rw [hF'card, hk]
      unfold GGHasLabel
      dsimp only [LargeEvenRawDatum]
      refine ⟨F', hF', hF'fin, hF'card', ?_⟩
      exact ⟨eJ.trans eK'⟩
  refine ⟨hXc, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R' _ I' F' ⟨hs', hna', θ', hP', _⟩
  exact ⟨hs', hna', θ', hP', hmain⟩

end CFSG.StandardType

end
