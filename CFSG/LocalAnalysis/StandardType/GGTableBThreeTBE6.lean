module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBTv
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBModel
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDE6Field
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Cfg
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Nbr
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSix
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredDef
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLModPSL
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Act

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBE6DivLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1

theorem GGTableBE6DivLabel.three {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBE6DivLabel p lab) : p = 3 ∧ 3 ∣ 2 ^ lab.n - 1 := by
  obtain ⟨-, rfl, h3⟩ := h
  exact ⟨rfl, h3⟩

@[expose] def GGE6DivTorusNbrInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    U63TB.GGTorusNbrSCrK 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)

@[expose] def GGE6DivModuleInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    GGTableBModuleSCr 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)

@[expose] def GGE6DivActionInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    GGTableBActionSCr 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)

@[expose] def GGE6DivTvInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    GGNoTransvectionSCr 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)

theorem ggNoInvariantLineSCr_of_ggTableBModuleSCr {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : 2 ≤ p) (h : GGTableBModuleSCr p r R I) :
    GGNoInvariantLineSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  obtain ⟨H, W, -, -, hcard, -, hW, hH⟩ := h L' ψ hψ hker hperf A hA hAI hr h3 hsc
  refine ⟨W, hW, fun Λ hΛA hΛp => ?_⟩
  by_contra hcon
  push Not at hcon
  have hΛ0 : Λ ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hΛp
    omega
  have h1 : Nat.card H ≤ Nat.card Λ := Subgroup.card_le_of_le (hH Λ hΛA hΛ0 hcon)
  have h2 : Nat.card A ≤ p * p :=
    calc Nat.card A ≤ p * Nat.card H := hcard
      _ ≤ p * Nat.card Λ := Nat.mul_le_mul_left p h1
      _ = p * p := by rw [hΛp]
  have h4 : p * p < p ^ 3 := by
    have e : p ^ 3 = p * p * p := by ring
    rw [e]
    nlinarith
  exact absurd (le_trans h3 h2) (not_le.mpr h4)

section Certs33


theorem largeEvenLabelAll_e6Div_of {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ 2 ^ lab.n - 1)
    {P : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (hP : ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      3 ∣ 2 ^ n - 1 → P (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 5 R ∧ P R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag h3 hn
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK, hl⟩ := TableBExc.recipeChevalleyE6_torusLift_three h3 hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQK, hl, hP K n hn hK h3⟩

theorem largeEvenLabelAll_e6Div_nbr {lab : LargeEvenLabel} (hK : GGE6DivTorusNbrInput)
    (htag : lab.tag = .E6) (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 5 R ∧ U63TB.GGTorusNbrSCrK 3 5 R I :=
  largeEvenLabelAll_e6Div_of (P := fun R _ I => U63TB.GGTorusNbrSCrK 3 5 R I) htag hlab h3
    (fun K _ _ n hn hK' h => hK K n hn hK' h)

theorem largeEvenLabelAll_e6Div_mod {lab : LargeEvenLabel} (hK : GGE6DivModuleInput)
    (htag : lab.tag = .E6) (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 5 R ∧ GGTableBModuleSCr 3 5 R I :=
  largeEvenLabelAll_e6Div_of (P := fun R _ I => GGTableBModuleSCr 3 5 R I) htag hlab h3
    (fun K _ _ n hn hK' h => hK K n hn hK' h)

theorem largeEvenLabelAll_e6Div_act {lab : LargeEvenLabel} (hK : GGE6DivActionInput)
    (htag : lab.tag = .E6) (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 5 R ∧ GGTableBActionSCr 3 5 R I :=
  largeEvenLabelAll_e6Div_of (P := fun R _ I => GGTableBActionSCr 3 5 R I) htag hlab h3
    (fun K _ _ n hn hK' h => hK K n hn hK' h)

theorem largeEvenLabelAll_e6Div_tv {lab : LargeEvenLabel} (hK : GGE6DivTvInput)
    (htag : lab.tag = .E6) (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 5 R ∧ GGNoTransvectionSCr 3 5 R I :=
  largeEvenLabelAll_e6Div_of (P := fun R _ I => GGNoTransvectionSCr 3 5 R I) htag hlab h3
    (fun K _ _ n hn hK' h => hK K n hn hK' h)

theorem largeEvenLabelAll_e6Div_line {lab : LargeEvenLabel} (hK : GGE6DivModuleInput)
    (htag : lab.tag = .E6) (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 5 R ∧ GGNoInvariantLineSCr 3 5 R I :=
  largeEvenLabelAll_e6Div_of (P := fun R _ I => GGNoInvariantLineSCr 3 5 R I) htag hlab h3
    (fun K _ _ n hn hK' h => ggNoInvariantLineSCr_of_ggTableBModuleSCr (by norm_num)
      (hK K n hn hK' h))

theorem ggLTransvectionCenterInputOn_e6Div (hK : GGE6DivTvInput) :
    GGLTransvectionCenterInputOn GGTableBE6DivLabel := by
  intro G _ _ p B Bs x L D J hC hM φ hφ hφt b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBE6DivLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 5 R ∧ GGNoTransvectionSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_e6Div_tv hK hs.1 hlab (GGTableBE6DivLabel.three hs).2)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, htv⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨h5, h3'⟩ := card_range_ggGamma_bstar_ge hC hL θ hBsN hlift
  exact UnitTv.mem_zpowers_of_noTransvectionSCr_card hC
    (UnitTB.exists_noncyclic_of_torusLift hp (by norm_num) hL θ hlift) hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' htv hφ hφt b

theorem ggLNoInvariantLineInputOn_e6Div (hK : GGE6DivModuleInput) :
    GGLNoInvariantLineInputOn GGTableBE6DivLabel := by
  intro G _ _ p B Bs x L D J hC hM E hEBs hxE hE
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBE6DivLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 5 R ∧ GGNoInvariantLineSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_e6Div_line hK hs.1 hlab (GGTableBE6DivLabel.three hs).2)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨h5, h3'⟩ := card_range_ggGamma_bstar_ge hC hL θ hBsN hlift
  exact Line63.not_normalizer_le_of_noInvariantLineSCr_card hC hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT hEBs hxE hE

theorem ggLTransvectionCenterInputOn_of_not_e6Div (hK : GGE6DivTvInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGTableBE6DivLabel p lab) :
    GGLTransvectionCenterInputOn S := by
  have h' := (ggLTransvectionCenterInputOn_e6Div hK).or h
  intro G _ _ p B Bs x L D J hC hM
  refine h' G p B Bs x L D J hC (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBE6DivLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggLNoInvariantLineInputOn_of_not_e6Div (hK : GGE6DivModuleInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGTableBE6DivLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := (ggLNoInvariantLineInputOn_e6Div hK).or h
  intro G _ _ p B Bs x L D J hC hM
  refine h' G p B Bs x L D J hC (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBE6DivLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

end Certs33

section Certs34


theorem ggBstarInnerDiagLInputOn_e6Div (hY : GGE6InnerDiagBoundThreeInput) :
    GGBstarInnerDiagLInputOn GGTableBE6DivLabel := by
  have hF := ggBstarInnerDiagLInputOn_of_le_e6ThreeField hY
    (S := fun p lab => GGTableBE6DivLabel p lab ∧ p ∣ lab.n) (fun p lab h => by
      obtain ⟨⟨ht, rfl, hd⟩, hn⟩ := h
      exact ⟨ht, rfl, hd, hn⟩)
  have hC := CorFourTwoOpen.ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds
    (S := fun p lab => GGTableBE6DivLabel p lab ∧ ¬ p ∣ lab.n) (fun p lab hp hlab hs => by
      obtain ⟨⟨ht, rfl, -⟩, hn⟩ := hs
      exact NbrLangWeylRest.largeEvenLabelAll_pow_mem_e6 hp (by norm_num) hlab (Or.inl ht) hn)
  have h := hF.or hC
  have e : (fun p lab => (GGTableBE6DivLabel p lab ∧ p ∣ lab.n) ∨
      (GGTableBE6DivLabel p lab ∧ ¬ p ∣ lab.n)) = GGTableBE6DivLabel := by
    funext p lab
    apply propext
    by_cases hpn : p ∣ lab.n <;> simp [hpn]
  rwa [e] at h

theorem ggTableBCxInputOn_e6Div (hY : GGE6InnerDiagBoundThreeInput) (hK : GGE6DivTorusNbrInput) :
    GGTableBCxInputOn GGTableBE6DivLabel := by
  intro G _ _ p B Bs x L D J hcfg hM Y hYx hYN _ hYn hYp
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBE6DivLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 5 R ∧ U63TB.GGTorusNbrSCrK 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_e6Div_nbr hK hs.1 hlab (GGTableBE6DivLabel.three hs).2)
    (fun _ _ _ _ _ _ hP => hP.1)
    (ggBstarInnerDiagLInputOn_e6Div hY G p B Bs x L D J hcfg hM)
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨h5, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  exact U63TB.ggTableBCx_of_card hcfg
    (UnitTB.exists_noncyclic_of_torusLift hp (by norm_num) hL θ hlift) hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT hYx hYN hYn hYp

theorem ggTableBModuleInputOn_e6Div (hY : GGE6InnerDiagBoundThreeInput)
    (hK : GGE6DivModuleInput) : GGTableBModuleInputOn GGTableBE6DivLabel := by
  intro G _ _ p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBE6DivLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 5 R ∧ GGTableBModuleSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_e6Div_mod hK hs.1 hlab (GGTableBE6DivLabel.three hs).2)
    (fun _ _ _ _ _ _ hP => hP.1)
    (ggBstarInnerDiagLInputOn_e6Div hY G p B Bs x L D J hcfg hM)
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨h5, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  exact U63TB.ggTableBModule_of_card hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT

theorem ggTableBActionInputOn_e6Div (hY : GGE6InnerDiagBoundThreeInput)
    (hK : GGE6DivActionInput) : GGTableBActionInputOn GGTableBE6DivLabel := by
  intro G _ _ p B Bs x L D J B₂ hcfg hM hMod
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBE6DivLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 5 R ∧ GGTableBActionSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_e6Div_act hK hs.1 hlab (GGTableBE6DivLabel.three hs).2)
    (fun _ _ _ _ _ _ hP => hP.1)
    (ggBstarInnerDiagLInputOn_e6Div hY G p B Bs x L D J hcfg hM)
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨h5, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  exact U63TB.ggTableBAction_of_card hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT hMod

theorem ggTableBCxInputOn_of_not_e6Div (hY : GGE6InnerDiagBoundThreeInput)
    (hK : GGE6DivTorusNbrInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGTableBE6DivLabel p lab) :
    GGTableBCxInputOn S := by
  have h' := (ggTableBCxInputOn_e6Div hY hK).or h
  intro G _ _ p B Bs x L D J hcfg hM
  refine h' G p B Bs x L D J hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBE6DivLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_e6Div (hY : GGE6InnerDiagBoundThreeInput)
    (hK : GGE6DivModuleInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGTableBE6DivLabel p lab) :
    GGTableBModuleInputOn S := by
  have h' := (ggTableBModuleInputOn_e6Div hY hK).or h
  intro G _ _ p B Bs x L D J hcfg hM
  refine h' G p B Bs x L D J hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBE6DivLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_e6Div (hY : GGE6InnerDiagBoundThreeInput)
    (hK : GGE6DivActionInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGTableBE6DivLabel p lab) :
    GGTableBActionInputOn S := by
  have h' := (ggTableBActionInputOn_e6Div hY hK).or h
  intro G _ _ p B Bs x L D J B₂ hcfg hM
  refine h' G p B Bs x L D J B₂ hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBE6DivLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

end Certs34

end CFSG.StandardType

end
