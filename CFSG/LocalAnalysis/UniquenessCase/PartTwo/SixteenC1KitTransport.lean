module

import CFSG.LocalAnalysis.EvenBN.TrialityD4.Invariants

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitStruct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitModel
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Om6
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124BlkTransfer
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62

private noncomputable def s16c1_kappa {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) : (V₀ ≃ₗ[ZMod 2] V₀) →* MulAut W where
  toFun g := β.trans ((AddEquiv.toMultiplicative g.toAddEquiv).trans β.symm)
  map_one' := by ext x; simp
  map_mul' := by
    intro g h
    ext x
    simp [LinearEquiv.mul_apply, MulEquiv.trans_apply, AddEquiv.toMultiplicative_apply_apply]

private lemma s16c1_kappa_apply {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    (g : V₀ ≃ₗ[ZMod 2] V₀) (x : W) :
    β (s16c1_kappa β g x) =
      Multiplicative.ofAdd (g (Multiplicative.toAdd (β x))) := by
  simp [s16c1_kappa, MulEquiv.trans_apply, AddEquiv.toMultiplicative_apply_apply]

private lemma s16c1_kappa_injective {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀) :
    Function.Injective (s16c1_kappa β) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro v
  have h1 := congrArg (fun φ : MulAut W => β (φ (β.symm (Multiplicative.ofAdd v)))) hgh
  simpa [s16c1_kappa_apply] using h1

private lemma s16c1_mem_H_iff {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (φ : MulAut W) :
    φ ∈ H ↔ ∃ g ∈ Ω₀ true, φ = s16c1_kappa β g := by
  rw [hβ φ]
  constructor
  · rintro ⟨g, hg, hgφ⟩
    refine ⟨g, hg, ?_⟩
    ext x
    exact β.injective (by rw [hgφ x, s16c1_kappa_apply])
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun x => s16c1_kappa_apply β g x⟩

private lemma s16c1_kappa_mem_ptCent {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (z : W)
    (g : V₀ ≃ₗ[ZMod 2] V₀) :
    s16c1_kappa β g ∈ ptCent H z ↔
      g ∈ Ω₀ true ∧ g (Multiplicative.toAdd (β z)) = Multiplicative.toAdd (β z) := by
  rw [ptCent, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  constructor
  · rintro ⟨hH, hfix⟩
    obtain ⟨g', hg', heq⟩ := (s16c1_mem_H_iff hβ (s16c1_kappa β g)).1 hH
    have hgg' : g = g' := s16c1_kappa_injective β heq
    refine ⟨?_, ?_⟩
    · rw [hgg']; exact hg'
    · apply Multiplicative.ofAdd.injective
      have h1 := congrArg β hfix
      rw [s16c1_kappa_apply] at h1
      simpa using h1
  · rintro ⟨hg, hgz⟩
    refine ⟨(s16c1_mem_H_iff hβ _).2 ⟨g, hg, rfl⟩, ?_⟩
    apply β.injective
    rw [s16c1_kappa_apply]
    simpa using congrArg Multiplicative.ofAdd hgz

theorem s16c1_omegaGeo2_of_model {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaGeo2 H := by
  intro P hP
  let Pa : AddSubgroup V₀ := Subgroup.toAddSubgroup' (P.map β.toMonoidHom)
  have hcardPa : Nat.card Pa = 4 := by
    have h2 : Nat.card Pa = Nat.card (P.map β.toMonoidHom) :=
      CFSG.LocalAnalysis.EvenBN.TrialityD4.TrialityD4Data.card_toAddSubgroup'_eq
        (P.map β.toMonoidHom)
    have h1 : Nat.card (P.map β.toMonoidHom) = Nat.card P :=
      Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective
    rw [h2, h1, hP]
  obtain ⟨g, hg, hgord, hgfix⟩ := s16c1_omega0_geo2 Pa hcardPa
  refine ⟨s16c1_kappa β g, (s16c1_mem_H_iff hβ _).2 ⟨g, hg, rfl⟩, ?_, ?_⟩
  · rw [orderOf_injective (s16c1_kappa β) (s16c1_kappa_injective β) g]
    exact hgord
  · intro p hp
    apply β.injective
    rw [s16c1_kappa_apply]
    have hpmem : Multiplicative.toAdd (β p) ∈ Pa := by
      rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_map_equiv]
      simpa using hp
    rw [hgfix _ hpmem]
    rfl

theorem s16c1_omegaIrr_of_model {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaIrr H := by
  intro z hz h960 S hS
  let z' : V₀ := Multiplicative.toAdd (β z)
  have hz' : z' ≠ 0 := by
    intro h
    apply hz
    apply β.injective
    rw [map_one]
    simpa [z'] using congrArg Multiplicative.ofAdd h
  let f : {g : ↥(Ω₀ true) // (g : V₀ ≃ₗ[ZMod 2] V₀) z' = z'} → ↥(ptCent H z) :=
    fun g => ⟨s16c1_kappa β g.1, (s16c1_kappa_mem_ptCent hβ z g.1).2 ⟨g.1.2, g.2⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have h := congrArg (fun φ : ↥(ptCent H z) => (φ : MulAut W)) hab
      exact Subtype.ext (Subtype.ext (s16c1_kappa_injective β h))
    · intro y
      have hyH : y.1 ∈ H := (Subgroup.mem_inf.mp y.2).1
      obtain ⟨g, hg, hgy⟩ := (s16c1_mem_H_iff hβ y.1).1 hyH
      have hmem : s16c1_kappa β g ∈ ptCent H z := hgy ▸ y.2
      have hgz : g z' = z' := ((s16c1_kappa_mem_ptCent hβ z g).1 hmem).2
      exact ⟨⟨⟨g, hg⟩, hgz⟩, Subtype.ext hgy.symm⟩
  have h960' :
      Nat.card {g : ↥(Ω₀ true) // (g : V₀ ≃ₗ[ZMod 2] V₀) z' = z'} = 960 := by
    rw [Nat.card_congr (Equiv.ofBijective f hbij), h960]
  let Sa : AddSubgroup V₀ := Subgroup.toAddSubgroup' (S.map β.toMonoidHom)
  have hcardSa : Nat.card Sa = Nat.card S := by
    have h1 : Nat.card Sa = Nat.card (S.map β.toMonoidHom) :=
      CFSG.LocalAnalysis.EvenBN.TrialityD4.TrialityD4Data.card_toAddSubgroup'_eq
        (S.map β.toMonoidHom)
    have h2 : Nat.card (S.map β.toMonoidHom) = Nat.card S :=
      Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective
    rw [h1, h2]
  have hSa : ∀ g ∈ Ω₀ true, g z' = z' → ∀ s ∈ Sa, g s ∈ Sa := by
    intro g hg hgz s hs
    rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_map_equiv] at hs ⊢
    have hmem : s16c1_kappa β g ∈ ptCent H z :=
      (s16c1_kappa_mem_ptCent hβ z g).2 ⟨hg, hgz⟩
    have hkey : s16c1_kappa β g (β.symm (Multiplicative.ofAdd s)) =
        β.symm (Multiplicative.ofAdd (g s)) := by
      apply β.injective
      rw [s16c1_kappa_apply, MulEquiv.apply_symm_apply]
      simp
    have h1 := hS _ hmem _ hs
    rwa [hkey] at h1
  have hres := s16c1_omega0_irr hz' h960' Sa hSa
  rw [hcardSa] at hres
  exact hres

theorem s16c1_omegaNoTrans_of_model {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaNoTrans H := by
  intro t ht c hc htrans
  obtain ⟨g, hg, rfl⟩ := (s16c1_mem_H_iff hβ t).1 ht
  have hc' : Multiplicative.toAdd (β c) ≠ 0 := by
    intro h
    apply hc
    apply β.injective
    rw [map_one]
    simpa using congrArg Multiplicative.ofAdd h
  have hgfix : ∀ v : V₀, g v = v ∨ g v = v + Multiplicative.toAdd (β c) := by
    intro v
    have hx := htrans (β.symm (Multiplicative.ofAdd v))
    have hβx : β (β.symm (Multiplicative.ofAdd v)) = Multiplicative.ofAdd v :=
      MulEquiv.apply_symm_apply β _
    rcases hx with hx | hx
    · left
      apply Multiplicative.ofAdd.injective
      have h1 := congrArg β hx
      rw [s16c1_kappa_apply, hβx] at h1
      simpa using h1
    · right
      apply Multiplicative.ofAdd.injective
      have h1 := congrArg β hx
      rw [s16c1_kappa_apply, hβx, map_mul, hβx] at h1
      simpa using h1
  have hg1 : g = 1 := s16c1_omega0_noTrans hg hc' hgfix
  rw [hg1, map_one]

theorem omegaKit_holds : OmegaKit := by
  intro W _ _ H h
  obtain ⟨β, hβ⟩ := natOmegaMinus_exists_model h
  exact ⟨s16c1_omegaGeo2_of_model hβ, s16c1_omegaIrr_of_model hβ,
    s16c1_omegaNoTrans_of_model hβ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
