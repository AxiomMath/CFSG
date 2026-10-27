module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Form
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Sing
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Sym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62

noncomputable def s16c1G_kappa {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) : (V₀ ≃ₗ[ZMod 2] V₀) →* MulAut W where
  toFun g := β.trans ((AddEquiv.toMultiplicative g.toAddEquiv).trans β.symm)
  map_one' := by ext x; simp
  map_mul' := by
    intro g h
    ext x
    simp [LinearEquiv.mul_apply, MulEquiv.trans_apply, AddEquiv.toMultiplicative_apply_apply]

theorem s16c1G_kappa_apply {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    (g : V₀ ≃ₗ[ZMod 2] V₀) (x : W) :
    β (s16c1G_kappa β g x) = Multiplicative.ofAdd (g (Multiplicative.toAdd (β x))) := by
  simp [s16c1G_kappa, MulEquiv.trans_apply, AddEquiv.toMultiplicative_apply_apply]

theorem s16c1G_kappa_injective {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀) :
    Function.Injective (s16c1G_kappa β) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro v
  have h1 := congrArg (fun φ : MulAut W => β (φ (β.symm (Multiplicative.ofAdd v)))) hgh
  simpa [s16c1G_kappa_apply] using h1

theorem s16c1G_mem_H_iff {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (φ : MulAut W) :
    φ ∈ H ↔ ∃ g ∈ Ω₀ true, φ = s16c1G_kappa β g := by
  rw [hβ φ]
  constructor
  · rintro ⟨g, hg, hgφ⟩
    refine ⟨g, hg, ?_⟩
    ext x
    exact β.injective (by rw [hgφ x, s16c1G_kappa_apply])
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun x => s16c1G_kappa_apply β g x⟩

theorem s16c1G_kappa_mem_ptCent {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (z : W)
    (g : V₀ ≃ₗ[ZMod 2] V₀) :
    s16c1G_kappa β g ∈ ptCent H z ↔
      g ∈ Ω₀ true ∧ g (Multiplicative.toAdd (β z)) = Multiplicative.toAdd (β z) := by
  rw [ptCent, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  constructor
  · rintro ⟨hH, hfix⟩
    obtain ⟨g', hg', heq⟩ := (s16c1G_mem_H_iff hβ (s16c1G_kappa β g)).1 hH
    have hgg' : g = g' := s16c1G_kappa_injective β heq
    refine ⟨?_, ?_⟩
    · rw [hgg']
      exact hg'
    · apply Multiplicative.ofAdd.injective
      have h1 := congrArg β hfix
      rw [s16c1G_kappa_apply] at h1
      simpa using h1
  · rintro ⟨hg, hgz⟩
    refine ⟨(s16c1G_mem_H_iff hβ _).2 ⟨g, hg, rfl⟩, ?_⟩
    apply β.injective
    rw [s16c1G_kappa_apply]
    simpa using congrArg Multiplicative.ofAdd hgz

noncomputable def s16c1G_ptCentHom {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (w : W) :
    ↥(MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd (β w))) →* ↥(ptCent H w) where
  toFun g := ⟨s16c1G_kappa β (g.1 : V₀ ≃ₗ[ZMod 2] V₀),
    (s16c1G_kappa_mem_ptCent hβ w g.1).2 ⟨g.1.2, s16c1G_stab_apply g⟩⟩
  map_one' := Subtype.ext (map_one (s16c1G_kappa β))
  map_mul' g h := Subtype.ext (map_mul (s16c1G_kappa β) _ _)

theorem s16c1G_ptCentHom_bijective {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (w : W) :
    Function.Bijective (s16c1G_ptCentHom hβ w) := by
  constructor
  · intro a b hab
    have h := congrArg (fun φ : ↥(ptCent H w) => (φ : MulAut W)) hab
    exact Subtype.ext (Subtype.ext (s16c1G_kappa_injective β h))
  · intro y
    have hyH : y.1 ∈ H := (Subgroup.mem_inf.mp y.2).1
    obtain ⟨g, hg, hgy⟩ := (s16c1G_mem_H_iff hβ y.1).1 hyH
    have hmem : s16c1G_kappa β g ∈ ptCent H w := hgy ▸ y.2
    have hgz : g (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (β w) :=
      ((s16c1G_kappa_mem_ptCent hβ w g).1 hmem).2
    exact ⟨⟨⟨g, hg⟩, hgz⟩, Subtype.ext hgy.symm⟩

noncomputable def s16c1G_ptCentEquiv {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (w : W) :
    ↥(MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd (β w))) ≃* ↥(ptCent H w) :=
  MulEquiv.ofBijective (s16c1G_ptCentHom hβ w) (s16c1G_ptCentHom_bijective hβ w)

theorem s16c1G_toAdd_ne_zero {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀) {w : W}
    (hw : w ≠ 1) : Multiplicative.toAdd (β w) ≠ 0 := by
  intro h
  apply hw
  apply β.injective
  rw [map_one]
  simpa using congrArg Multiplicative.ofAdd h

theorem s16c1G_qModel_cases (z : V₀) : qModel true z = 0 ∨ qModel true z = 1 :=
  zmod2_eq_zero_or_eq_one _

theorem s16c1G_omegaFormExists_of_model {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaFormExists H := by
  refine ⟨fun x => qModel true (Multiplicative.toAdd (β x)),
    s16c1G_isMinusQuadF2_comp β s16c1G_isMinusQuadF2_qMul, fun φ hφ x => ?_⟩
  obtain ⟨g, hg, hgφ⟩ := (hβ φ).1 hφ
  show qModel true (Multiplicative.toAdd (β (φ x))) = qModel true (Multiplicative.toAdd (β x))
  rw [hgφ x]
  exact s16c1G_qModel_map hg _

theorem s16c1G_omegaSingE16A5_of_model {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaSingE16A5 H := by
  intro w hw h960
  have hz := s16c1G_toAdd_ne_zero β hw
  have hcard : Nat.card (MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd (β w))) = 960 := by
    rw [Nat.card_congr (s16c1G_ptCentEquiv hβ w).toEquiv, h960]
  have hq : qModel true (Multiplicative.toAdd (β w)) = 0 := by
    rcases s16c1G_qModel_cases (Multiplicative.toAdd (β w)) with h | h
    · exact h
    · rw [s16c1G_card_stab_nonsing h] at hcard
      omega
  exact s16c1G_isE16A5_congr (s16c1G_ptCentEquiv hβ w) (s16c1G_isE16A5_stab_sing hz hq)

theorem s16c1G_omegaNonsSym_of_model {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaNonsSym H := by
  intro w hw hne
  have hz := s16c1G_toAdd_ne_zero β hw
  have hq : qModel true (Multiplicative.toAdd (β w)) = 1 := by
    rcases s16c1G_qModel_cases (Multiplicative.toAdd (β w)) with h | h
    · exfalso
      apply hne
      rw [← Nat.card_congr (s16c1G_ptCentEquiv hβ w).toEquiv]
      exact s16c1G_card_stab_sing hz h
    · exact h
  exact s16c1G_isSym_congr (s16c1G_ptCentEquiv hβ w) (s16c1G_isSym_stab_nonsing hq)

theorem omegaKitF_holds : OmegaKitF := by
  intro W _ _ H h
  obtain ⟨β, hβ⟩ := natOmegaMinus_exists_model h
  exact ⟨s16c1G_omegaFormExists_of_model hβ, s16c1G_omegaSingE16A5_of_model hβ,
    s16c1G_omegaNonsSym_of_model hβ⟩

section Result

variable {G : Type} [Group G] [Finite G]

theorem r16_41_of_kitC (D : Data G) (h61 : UC6.R6_1 D) (hkitC : OmegaKitC) : R16_41 D :=
  r16_41_of D h61 hkitC omegaKitF_holds

end Result

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
