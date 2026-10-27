module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflOfLabel
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.StandardType.SpJoin CFSG.StandardType.SpJoinRefl

private theorem spn_hasLabel_C_of_lift {G : Type} [Group G] {J : Subgroup G} {m f : ℕ}
    (hZ : Subgroup.center J = ⊥) (ψ : StatedSp m (GaloisField 2 f) →* G)
    (hψ : Function.Injective ψ) (hψJ : ψ.range = J) (hm : 1 ≤ m) (hf : 1 ≤ f) :
    GGHasLabel ⟨.C, m, f⟩ (J ⧸ Subgroup.center J) := by
  haveI : NeZero m := ⟨by omega⟩
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let e₁ : (J ⧸ Subgroup.center J) ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e₂ : J ≃* StatedSp m (GaloisField 2 f) :=
    ((MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hψJ)).symm
  exact ⟨GaloisField 2 f, inferInstance, inferInstance, hcard,
    ⟨e₁.trans (e₂.trans (CFSG.SeitzReduction.F4Pilot.spProjEquiv m (GaloisField 2 f)))⟩⟩

private theorem spn_statedClassicalModel_of_hasLabel_C {X : Type} [Group X] {n f : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) (hX : GGHasLabel ⟨.C, n, f⟩ X) : StatedClassicalModel X .PSp n 2 f := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  refine ⟨⟨Nat.prime_two, hf, by omega, ?_⟩, K, hF, hfin, hK, ⟨e⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  omega

private theorem spn_hasLabel_C_of_statedModel {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSp n 2 f) : GGHasLabel ⟨.C, n, f⟩ X := by
  obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  exact ⟨K, hF, hfin, hcard, ⟨e⟩⟩

private theorem spn_bc_of_ggLabelIso_C {lab : LargeEvenLabel} {m f : ℕ}
    (h : GGLabelIso lab ⟨.C, m, f⟩) :
    (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = m ∧ lab.n = f := by
  rcases h with h | h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · subst h
    exact ⟨Or.inr rfl, rfl, rfl⟩
  · exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  all_goals simp at h

private theorem spn_tag_F4_of_ggLabelIso {lab : LargeEvenLabel} {f : ℕ}
    (h : GGLabelIso lab ⟨.F4, 0, f⟩) : lab.tag = .F4 := by
  rcases h with h | h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rw [h]
  · rcases h.2.1 with h' | h' <;> simp at h'
  all_goals simp at h

private theorem spn_tableP_row_of_tag_BC {p : ℕ} {J X : LargeEvenLabel}
    (hBC : J.tag = .B ∨ J.tag = .C) (h : GGTablePRow p J X) :
    X = ⟨.C, J.rank + 1, J.n⟩ ∨ (J.rank = 3 ∧ X = ⟨.F4, 0, J.n⟩) := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨-, -, -, hX⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  all_goals first
    | exact hX
    | (exfalso
       rcases hBC with hB | hB <;> rw [hB] at h1 <;> simp at h1)
    | (exfalso
       have ht := congrArg LargeEvenLabel.tag h1
       rcases hBC with hB | hB <;> rw [hB] at ht <;> simp at ht)

theorem ggSpNbr_type_or_F4_of_tableP_narrow
    (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hTPn : GGNbrTablePNbrInputOnL GGRegimeBCL) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ} {y : G} {K : Subgroup G}
    {y' : G} {K' : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) (hK' : GGNbr p B x D J y' K') :
    StatedClassicalModel (K' ⧸ Subgroup.center K') .PSp (m + 1) 2 f ∨
      (m = 3 ∧ LargeEvenMarking K' (fun lab _ _ I _ θ => lab.tag = .F4 ∧
        Bs ≤ Subgroup.normalizer (K' : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) := by
  obtain ⟨-, -, -, -, -, -, hZ, ψ, hψ, hψJ⟩ :=
    ggSpNbr_J_facts ggSpLiftInput_holds ggInnerDiagMpInput_holds hLB hJp hcfg hOp hInn hNoTr hN hK'
  have hm : 3 ≤ m := by
    have := hN.2.1
    omega
  have hf : 1 ≤ f := hN.1.1.2.1
  have hlabJ : GGHasLabel ⟨.C, m, f⟩ (J ⧸ Subgroup.center J) :=
    spn_hasLabel_C_of_lift hZ ψ hψ hψJ (by omega) hf
  have hΛJ : LargeEvenInLambda2 ⟨.C, m, f⟩ :=
    ⟨hf, show 2 ≤ m by omega, fun h => absurd (show m = 2 from h) (by omega)⟩
  have hΛL : LargeEvenInLambda2 (⟨.C, m + 1, f⟩ : LargeEvenLabel) :=
    ⟨hf, show 2 ≤ m + 1 by omega, fun h => absurd (show m + 1 = 2 from h) (by omega)⟩
  have hlabL : GGHasLabel (⟨.C, m + 1, f⟩ : LargeEvenLabel) (L ⧸ Subgroup.center L) :=
    spn_hasLabel_C_of_statedModel hN.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hInn.2 y' K' hK'
  have hHas : GGHasLabel lab (K' ⧸ Subgroup.center K') :=
    largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.2.2.choose⟩) hraw
  have hreg : GGRegimeBCL p (Nat.card Bs) (⟨.C, m + 1, f⟩ : LargeEvenLabel) ⟨.C, m, f⟩ lab :=
    ⟨Or.inr rfl, hm, Or.inr rfl, rfl, rfl⟩
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hJ', hK'lab⟩ :=
    hTPn G p B Bs x L D J y' K' hcfg hInn.1 (hInn.2 y' K' hK') hK' (⟨.C, m + 1, f⟩ : LargeEvenLabel)
      ⟨.C, m, f⟩ lab hΛL hΛJ hlab hreg hlabL hlabJ hHas
  obtain ⟨hBC, hrk, hn⟩ :=
    spn_bc_of_ggLabelIso_C (ggLabelRigidInput_holds labJ' ⟨.C, m, f⟩ (J ⧸ Subgroup.center J) hΛJ'
      hΛJ hJ' hlabJ)
  rcases spn_tableP_row_of_tag_BC hBC hrow with hX | ⟨h3, hX⟩
  ·
    left
    rw [hX, hrk, hn] at hK'lab
    exact spn_statedClassicalModel_of_hasLabel_C (by omega) hf hK'lab
  ·
    right
    refine ⟨hrk ▸ h3, ?_⟩
    rw [hX, hn] at hK'lab
    rw [hX, hn] at hΛK'
    have hF4 : lab.tag = .F4 :=
      spn_tag_F4_of_ggLabelIso (ggLabelRigidInput_holds lab ⟨.F4, 0, f⟩ (K' ⧸ Subgroup.center K')
        hlab hΛK' hHas hK'lab)
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨hs, hna, θ, hF4, hP⟩

theorem ggSpNbr_apriori_of_tableP_narrow
    (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hTPn : GGNbrTablePNbrInputOnL GGRegimeBCL) (hF4X : GGF4NbrAutReflXiKGInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ}
    {y : G} {K : Subgroup G} {y' : G} {K' : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hOp : GGOpAutTrivial p Bs) (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) (hK' : GGNbr p B x D J y' K') :
    GGReflGenerated p (ggAutomizer K' Bs) ∧
      2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer K' Bs) ∧
      ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K' Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y' := by
  rcases ggSpNbr_type_or_F4_of_tableP_narrow hLB hJp hTPn hcfg hOp hInn hNoTr hN hK' with
    hT | ⟨hm3, hmk⟩
  · exact ggSpNbr_apriori_sp hLB hJp hcfg hOp hInn hNoTr hN hK' hT
  · exact ggSpNbr_apriori_F4 hLB hJp hF4X hcfg hOp hInn hNoTr hN hK' hm3 hmk

theorem ggSpNbr_eq_of_label_of_tableP_narrow
    (hd : GGCoxeterLabelInput) (hLB : GGLBalanceInput)
    (hJp : GGStdSubPrimeInput) (hTPn : GGNbrTablePNbrInputOnL GGRegimeBCL)
    (hF4X : GGF4NbrAutReflXiKGInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} {y' : G} {K' : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J n f y K) (hK' : GGNbr p B x D J y' K') : K' = K := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hN.2.1; omega⟩
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hm : 4 ≤ m + 1 := hN.2.1
  obtain ⟨hRG, hcR, hCR⟩ :=
    ggSpNbr_apriori_of_tableP_narrow hLB hJp hTPn hF4X hcfg hOp hInn hNoTr hN hK'
  have hW : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) :=
    hd G p B Bs x L D J hcfg hOp hInn hNoTr y' K' hK' hRG (Or.inl hN.2.2.1)
  obtain ⟨hrank, hcL, hcK⟩ :=
    ggSpConfig_rank_orders ggSpLiftInput_holds ggInnerDiagMpInput_holds hcfg hInn hN
  obtain ⟨hxBs, hxL⟩ := hcfg.x_facts
  obtain ⟨hyBs, hyK, hyD, hyx, hx1⟩ := GGNbr.facts hcfg hN.2.2.2.1
  obtain ⟨hy'Bs, hy'K', hy'D, hy'x, -⟩ := GGNbr.facts hcfg hK'
  have hfx : ∀ ψ ∈ ggAutomizer L Bs, ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = x :=
    ggAutomizer_fixes_of_mem_centralizer hxBs hxL
  have hfy : ∀ ψ ∈ ggAutomizer K Bs, ((ψ ⟨y, hyBs⟩ : ↥Bs) : G) = y :=
    ggAutomizer_fixes_of_mem_centralizer hyBs hyK
  have hfy' : ∀ ψ ∈ ggAutomizer K' Bs, ((ψ ⟨y', hy'Bs⟩ : ↥Bs) : G) = y' :=
    ggAutomizer_fixes_of_mem_centralizer hy'Bs hy'K'
  have hy'xy : y' ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [← hN.2.2.2.1.2.1]
    exact hy'D
  have hind : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K' Bs, φ ∈ ggInduced ⊤ Bs := by
    have hle : ggAutomizer L Bs ⊔ ggAutomizer K' Bs ≤ ggInducedSubgroup ⊤ Bs :=
      sup_le (fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ)
        (fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ)
    exact fun φ hφ => hle hφ
  have hyy : Subgroup.zpowers y' = Subgroup.zpowers y :=
    ggSpLine_of_weylJoin hp hp2 hm hBs.2.1 hrank hNoTr hN.2.2.2.2.2 hxBs hyBs hy'Bs hfx hfy hfy'
      hcL hcK hcR (fun b hb => hCR b hb) hx1 hyx hy'x hy'xy hind hW
  exact (ggNbr_unique hLB hcfg.1 hcfg.2.2 (hJp G p B x L D J hcfg.1 hcfg.2.2) hN.2.2.2.1 hK'
    hyy.symm).symm

theorem ggSpJoinReflInput_of_label_tableP_narrow
    (hd : GGCoxeterLabelInput) (hLB : GGLBalanceInput)
    (hJp : GGStdSubPrimeInput) (hTPn : GGNbrTablePNbrInputOnL GGRegimeBCL)
    (hF4X : GGF4NbrAutReflXiKGInput) : GGSpJoinReflInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK'
  rw [ggSpNbr_eq_of_label_of_tableP_narrow hd hLB hJp hTPn hF4X hcfg hOp hInn hNoTr hN hK']
  exact le_sup_right

theorem ggSpJoinAutInput_of_label_tableP_narrow
    (hd : GGCoxeterLabelInput) (hLB : GGLBalanceInput)
    (hJp : GGStdSubPrimeInput) (hTPn : GGNbrTablePNbrInputOnL GGRegimeBCL)
    (hF4X : GGF4NbrAutReflXiKGInput) : GGSpJoinAutInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK' _
  rw [ggSpNbr_eq_of_label_of_tableP_narrow hd hLB hJp hTPn hF4X hcfg hOp hInn hNoTr hN hK']
  exact le_sup_right

end CFSG.StandardType

end
