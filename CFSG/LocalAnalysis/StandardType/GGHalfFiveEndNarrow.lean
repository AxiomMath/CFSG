module

public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveConjFive
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAlphaZeta
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnerDiag
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAutNb
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveSl4Model
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbrBasic
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGHalfFivePerm
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveLevi
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveGraph
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNoGraph
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private theorem hf5n_statedModel_of_equiv_sl6 {Y : Type} [Group Y]
    (e : Y ≃* Matrix.SpecialLinearGroup (Fin 6) F2) :
    Open.StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 6 2 1 := by
  refine ⟨?_, F2, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · unfold Open.StatedLieAdmissible
    norm_num
  · exact GaloisField.card 2 1 (by norm_num)
  · exact (QuotientGroup.congr (Subgroup.center Y)
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F2)) e
      (Subgroup.map_center_eq e)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 6 F2)

namespace GGHalfCtx

private theorem hf5n_eq_A22_of_ggLabelIso {lab : LargeEvenLabel}
    (hiso : GGLabelIso lab ⟨.A, 2, 2⟩) : lab = ⟨.A, 2, 2⟩ := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · exact absurd h.2.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)

theorem nb_equiv_sl4_narrow {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)
    (hRig : GGLabelRigidInput) (hTP : GGNbrTablePNbrInputOnL GGRegimeA24L)
    (hB : GGTableBAut48LeInput) (hM : GGL44CenterTrivialInput) (hAut : GGHalfAutWithin Bs L K)
    {N : Subgroup G}
    (hN : GGNbr p B x (dPrime x φ₁ φ₂) (sl3four.map φ₁) (bElt φ₁ φ₂) N)
    (hL₁ : sl3four.map φ₁ ≤ N) (hK₁ : sl3four.map φ₂ ≤ N) :
    Nonempty (↥N ≃* SpecialLinearGroup (Fin 4) (GaloisField 2 2)) := by
  obtain rfl : p = 3 := h.nbr.2.1
  obtain ⟨hThmI, hBstar, -⟩ := h.cfg
  have hcfg : GGConfig 3 B Bs x L (dPrime x φ₁ φ₂) (sl3four.map φ₁) :=
    ⟨hThmI, hBstar, stdSub_lb h⟩
  have hinnN : GGInnerDiagOn Bs N := innerDiag_nb h hN hL₁ hK₁
  have eL : ↥L ≃* SpecialLinearGroup (Fin 6) F2 :=
    ((MonoidHom.ofInjective h.coords.inj₁).trans
      (MulEquiv.subgroupCongr h.coords.range₁)).symm
  have hmodL : Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 6 2 1 :=
    hf5n_statedModel_of_equiv_sl6 eL
  have hhasL : GGHasLabel (⟨.A, 5, 1⟩ : LargeEvenLabel) (L ⧸ Subgroup.center L) :=
    ggHasLabel_typeA (n := 5) (f := 1) hmodL
  have hΛL : LargeEvenInLambda2 (⟨.A, 5, 1⟩ : LargeEvenLabel) :=
    largeEvenInLambda2_typeA (n := 5) (f := 1) hmodL
  have eLb : ↥(sl3four.map φ₁) ≃* SpecialLinearGroup (Fin 3) F4 :=
    (sl3four.equivMapOfInjective φ₁ h.coords.inj₁).symm.trans sl3fourEquiv.symm
  have hmod : Open.StatedClassicalModel (↥(sl3four.map φ₁) ⧸ Subgroup.center ↥(sl3four.map φ₁))
      .PSL 3 2 2 :=
    statedModel_of_equiv_sl3 eLb
  have hhasJ₀ : GGHasLabel ⟨.A, 2, 2⟩
      (↥(sl3four.map φ₁) ⧸ Subgroup.center ↥(sl3four.map φ₁)) :=
    ggHasLabel_typeA hmod
  have hΛJ₀ : LargeEvenInLambda2 (⟨.A, 2, 2⟩ : LargeEvenLabel) :=
    largeEvenInLambda2_typeA hmod
  obtain ⟨labN, hΛN, hhasN, -⟩ := largeEvenMarking_exists_hasLabel hinnN
  obtain ⟨labJ', labN', hΛJ', hΛN', hrow, hhasJ', hhasN'⟩ :=
    hTP G 3 B Bs x L (dPrime x φ₁ φ₂) (sl3four.map φ₁) (bElt φ₁ φ₂) N
      hcfg h.inner.1 hinnN hN (⟨.A, 5, 1⟩ : LargeEvenLabel) (⟨.A, 2, 2⟩ : LargeEvenLabel) labN
      hΛL hΛJ₀ hΛN ⟨rfl, rfl, rfl⟩ hhasL hhasJ₀ hhasN
  have hiso : GGLabelIso labJ' (⟨.A, 2, 2⟩ : LargeEvenLabel) :=
    hRig labJ' (⟨.A, 2, 2⟩ : LargeEvenLabel)
      (↥(sl3four.map φ₁) ⧸ Subgroup.center ↥(sl3four.map φ₁)) hΛJ' hΛJ₀ hhasJ' hhasJ₀
  have hlabJ' : labJ' = ⟨.A, 2, 2⟩ := hf5n_eq_A22_of_ggLabelIso hiso
  have hBres := hB G B Bs x L (dPrime x φ₁ φ₂) (sl3four.map φ₁) (bElt φ₁ φ₂) N
    hcfg hN hinnN labJ' labN' hΛJ' hΛN' hhasJ' hhasN' hrow hlabJ'
  have hmodel : Open.StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2 := by
    rcases hBres with hmodel | h48
    · exact hmodel
    · exfalso
      have hle := card_automizer_nb_le h hAut hN
      omega
  have hq : CFSG.IsQuasisimple ↥N :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥N).mp
      (isQuasisimple_of_largeEvenMarking hinnN)
  have hcenter : Subgroup.center ↥N = ⊥ := hM ↥N hq hmodel
  obtain ⟨e⟩ := equiv_sl4_of_statedModel hmodel
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem no_graph_five_narrow {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)
    (hRig : GGLabelRigidInput) (hL : GGLBalanceInput)
    (hTP : GGNbrTablePNbrInputOnL GGRegimeA24L) (hB : GGTableBAut48LeInput)
    (hM : GGL44CenterTrivialInput) (hAut : GGHalfAutWithin Bs L K)
    {α : MulAut (SpecialLinearGroup (Fin 6) F2)}
    (hα : ∀ s, hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹ = gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹)
    (c : SpecialLinearGroup (Fin 6) F2)
    (hαc : α = MulAut.conj c *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2) : False := by
  obtain ⟨N, hN, hL₁, hK₁⟩ := h.exists_nb hL
  obtain ⟨e⟩ := h.nb_equiv_sl4_narrow hRig hTP hB hM hAut hN hL₁ hK₁
  have hζ : α zeta5 = zeta5 := h.alpha_zeta5 hα
  obtain ⟨α'', hα''res, htr⟩ := graph_case_restrict α c hαc hζ
  have hgN : gElt φ₁ ∈ N := hL₁ (Subgroup.mem_map_of_mem φ₁ slPerm_sigma_mem_sl3four)
  have hhN : hElt φ₂ ∈ N := hK₁ (Subgroup.mem_map_of_mem φ₂ slPerm_tau_mem_sl3four)
  set y₁ : G := (gElt φ₁)⁻¹ * hElt φ₂ with hy₁def
  have hy₁N : y₁ ∈ N := by rw [hy₁def]; exact N.mul_mem (N.inv_mem hgN) hhN
  let f₁ : SpecialLinearGroup (Fin 3) F4 →* ↥N :=
    (φ₁.comp (resSL 3)).codRestrict N
      (fun s => hL₁ (Subgroup.mem_map_of_mem φ₁ (MonoidHom.mem_range.mpr ⟨s, rfl⟩)))
  let f₂ : SpecialLinearGroup (Fin 3) F4 →* ↥N :=
    (φ₂.comp (resSL 3)).codRestrict N
      (fun s => hK₁ (Subgroup.mem_map_of_mem φ₂ (MonoidHom.mem_range.mpr ⟨s, rfl⟩)))
  let R₁ : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 4) F4 :=
    e.toMonoidHom.comp f₁
  let R₂ : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 4) F4 :=
    e.toMonoidHom.comp f₂
  set Y : SpecialLinearGroup (Fin 4) F4 := e ⟨y₁, hy₁N⟩ with hYdef
  have hR₁ : ∀ s, e.symm (R₁ s) = f₁ s := by
    intro s
    change e.symm (e (f₁ s)) = f₁ s
    exact MulEquiv.symm_apply_apply e (f₁ s)
  have hR₂ : ∀ s, e.symm (R₂ s) = f₂ s := by
    intro s
    change e.symm (e (f₂ s)) = f₂ s
    exact MulEquiv.symm_apply_apply e (f₂ s)
  have hY : e.symm Y = ⟨y₁, hy₁N⟩ := by
    rw [hYdef, MulEquiv.symm_apply_apply]
  have inj_f₁ : Function.Injective f₁ := by
    intro a b hab
    have h3 := congrArg Subtype.val hab
    change φ₁ (resSL 3 a) = φ₁ (resSL 3 b) at h3
    exact resSL_injective 3 (h.coords.inj₁ h3)
  have inj_f₂ : Function.Injective f₂ := by
    intro a b hab
    have h3 := congrArg Subtype.val hab
    change φ₂ (resSL 3 a) = φ₂ (resSL 3 b) at h3
    exact resSL_injective 3 (h.coords.inj₂ h3)
  have h₁ : Function.Injective R₁ := fun a b hab => inj_f₁ (e.injective hab)
  have h₂ : Function.Injective R₂ := fun a b hab => inj_f₂ (e.injective hab)
  have hconjG : ∀ u : SpecialLinearGroup (Fin 6) F2,
      y₁ * φ₁ (α u) * y₁⁻¹ = φ₂ u := by
    intro u
    rw [hy₁def]
    calc (gElt φ₁)⁻¹ * hElt φ₂ * φ₁ (α u) * ((gElt φ₁)⁻¹ * hElt φ₂)⁻¹
        = (gElt φ₁)⁻¹ * (hElt φ₂ * φ₁ (α u) * (hElt φ₂)⁻¹) * gElt φ₁ := by group
      _ = (gElt φ₁)⁻¹ * (gElt φ₁ * φ₂ u * (gElt φ₁)⁻¹) * gElt φ₁ := by rw [hα u]
      _ = φ₂ u := by group
  have hconj : ∀ s, Y * R₁ (α'' s) * Y⁻¹ = R₂ s := by
    intro s
    apply e.symm.injective
    simp only [map_mul, map_inv, hY, hR₁, hR₂]
    refine Subtype.ext ?_
    change y₁ * φ₁ (resSL 3 (α'' s)) * y₁⁻¹ = φ₂ (resSL 3 s)
    rw [← hα''res s]
    exact hconjG (resSL 3 s)
  have hagree : R₁ low5 = R₂ up5 := by
    apply e.symm.injective
    rw [hR₁ low5, hR₂ up5]
    refine Subtype.ext ?_
    change φ₁ (resSL 3 low5) = φ₂ (resSL 3 up5)
    obtain ⟨j, hj1, hj2⟩ := levi_agree_s5
    calc φ₁ (resSL 3 low5) = φ₁ (slLower2Hom 3 j) := by rw [hj1]
      _ = (φ₁.comp (slLower2Hom 3)) j := rfl
      _ = (φ₂.comp (slUpper2Hom 3)) j := by rw [h.coords.agree]
      _ = φ₂ (slUpper2Hom 3 j) := rfl
      _ = φ₂ (resSL 3 up5) := by rw [hj2]
  exact no_graph_case R₁ R₂ h₁ h₂ Y α'' htr hconj hagree

theorem alphaInner_five_narrow {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)
    (hRig : GGLabelRigidInput) (hL : GGLBalanceInput)
    (hTP : GGNbrTablePNbrInputOnL GGRegimeA24L) (hB : GGTableBAut48LeInput)
    (hM : GGL44CenterTrivialInput) (hAut : GGHalfAutWithin Bs L K) :
    GGHalfAlphaInner φ₁ φ₂ := by
  obtain ⟨α, hα⟩ := h.exists_alpha_five
  obtain ⟨c, ε, hε, hαc⟩ := aut_sl_gf2 (d := 3 + 1 + 1 + 1) (by omega) α
  interval_cases ε
  · refine ⟨c, fun s => ?_⟩
    have hα' : α = MulAut.conj c := by rw [hαc, pow_zero, mul_one]
    have hs : α s = c * s * c⁻¹ := by rw [hα', MulAut.conj_apply]
    rw [← hα s, hs]
  · exfalso
    have hα' : α = MulAut.conj c *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2 := by
      rw [hαc, pow_one]
    exact h.no_graph_five_narrow hRig hL hTP hB hM hAut hα c hα'

end GGHalfCtx

theorem ggHalfEndNodesFive_of_known_narrow (hH : GGTypeAHalfCoordInput) (hL : GGLBalanceInput)
    (hTP : GGNbrTablePNbrInputOnL GGRegimeA24L) (hB : GGTableBAut48LeInput)
    (hM : GGL44CenterTrivialInput) (hRig : GGLabelRigidInput) :
    GGHalfEndNodesOn (fun n => n = 5) := by
  intro G _ _ p B Bs x L D J n y K hn hcfg hOp hInn hNoTr hN hAut
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  obtain rfl : m = 3 := by omega
  obtain ⟨φ₁, φ₂, hco⟩ := hH G p B Bs x L D J 3 y K hcfg hInn hN
  have hctx : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂ := ⟨hcfg, hInn, hNoTr, hN, hco⟩
  obtain ⟨hT, hKle⟩ :=
    hctx.twoEndNodes
      (hctx.normSL014_of_alphaInner_of_three_le (by omega)
        (hctx.alphaInner_five_narrow hRig hL hTP hB hM hAut))
  have hmem : ∀ s, φ₂ s ∈ L ⊔ K := fun s =>
    Subgroup.mem_sup_right (hco.range₂ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩)
  refine ⟨φ₁, hco.range₁, ?_, endT₁ φ₂, endT₂ φ₂, hmem _, hmem _, hT, hKle⟩
  rw [(MonoidHom.ker_eq_bot_iff φ₁).mpr hco.inj₁]
  exact bot_le

end CFSG.StandardType

end
