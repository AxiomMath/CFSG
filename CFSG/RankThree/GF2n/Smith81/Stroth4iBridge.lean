module

public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondCases
public import CFSG.RankThree.GF2n.Smith81.OrthLaneClosed
public import CFSG.RankThree.GF2n.Tim81.RonanInputsHolds

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

@[expose] def Smith23E1LgenCtxStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), Ctx M Q Z B →
    t ∈ LB M Q B → t ∉ Q → CentTrivial M Q Z (Lgen M (LB M Q B)) → NoA2 Q Z (LB M Q B) →
    GenByB M Q B →
    (CaseE1Plus M Q Z B t → QuotSat (Lgen M (LB M Q B)) Q
      (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaPlus 2 (Nat.card Z)))) ∧
    (CaseE1Minus M Q Z B t → QuotSat (Lgen M (LB M Q B)) Q
      (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaMinus 2 (Nat.card Z))))

section Steps


theorem Smith23E1.smith23E1LgenCtx_of_steps (hS6 : Smith23E1.RtSplitStatement)
    (hR : Smith23E1.TheoremRStatement) (hP1 : Smith23E1.XNormalStatement) :
    Smith23E1LgenCtxStatement := by
  intro G _ _ M Q Z B t hc htL htQ hcent hno hgen
  have mk : CaseE1 M Q Z B t → E1Hyp M Q Z B t := fun hE => ⟨hc, htL, htQ, hcent, hE, hno, hgen⟩
  have hQN : Lgen M (LB M Q B) ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    hc.hyp.Q_normal.2 (Lgen_le_H0 hc hs).1
  have core : ∀ (hE : CaseE1 M Q Z B t) (P₂ : ∀ (W : Type) [Group W], Prop),
      QuotSat (E1Xpre M Q B t) Q P₂ →
        QuotSat (Lgen M (LB M Q B)) Q (IsProdOf (IsSLModel 2 (Nat.card Z)) P₂) := by
    intro hE P₂ hX
    have hH := mk hE
    obtain ⟨Y, hQY, hYL, -, hYX, hsup, hcomm, hY⟩ := hR G M Q Z B t hH (hP1 G M Q Z B t hH)
    exact internalProd_holds G _ Y (E1Xpre M Q B t) Q _ P₂ hQN hQY le_sup_right hYL
      (E1Xpre_le_Lgen hc htL) hYX hsup hcomm hY hX
  refine ⟨fun hE => ?_, fun hE => ?_⟩
  · have hE1 := (caseE1_iff M Q Z B t).mpr (Or.inl hE)
    obtain ⟨-, -, -, -, -, -, -, hXp, -⟩ := hS6 G M Q Z B t (mk hE1)
    exact core hE1 _ (hXp hE)
  · have hE1 := (caseE1_iff M Q Z B t).mpr (Or.inr hE)
    obtain ⟨-, -, -, -, -, -, -, -, hXm⟩ := hS6 G M Q Z B t (mk hE1)
    exact core hE1 _ (hXm hE)

theorem centTrivial_of_34_44 (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    CentTrivial M Q Z (Lgen M (LB M Q B)) := by
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  set T := Lgen M (LB M Q B) with hT
  have hLT : bar M Q (LB M Q B) ≤ bar M Q T :=
    Subgroup.map_mono (fun x hx => le_Lgen (LB M Q B) (show (x : G) ∈ LB M Q B from hx))
  have hnorm : bar M Q (LB M Q B) ≤ Subgroup.normalizer
      ((Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z) :
        Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
    intro g hg
    have hgT : g ∈ bar M Q T := hLT hg
    have hgc : g ∈ Subgroup.centralizer ((Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓
        bar M Q (H0 M Z) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp ha.1 g hgT).symm
    exact Subgroup.centralizer_le_normalizer _ hgc
  have hbot := h44 G M Q Z B hc n hw hn hno hgen
    (Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z)) inf_le_right hnorm
    (stroth_odd h34 G M Q Z B hc n hw hn hno hgen)
  intro h hh hcomm
  have hhM : h ∈ M := hh.1
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩ ∈
      Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z) := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ⟨⟨h, hhM⟩, show h ∈ H0 M Z from hh, rfl⟩⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : G) ∈ T := hs
    have hinv : (s : G)⁻¹ ∈ T := T.inv_mem hs'
    have hq : ⁅h, (s : G)⁻¹⁆ ∈ Q := hcomm _ hinv
    have e : QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩ * QuotientGroup.mk' (Q.subgroupOf M) s *
        (QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩)⁻¹ = QuotientGroup.mk' (Q.subgroupOf M) s := by
      rw [← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      show ((⟨h, hhM⟩ * s * ⟨h, hhM⟩⁻¹)⁻¹ * s : ↥M) ∈ Q.subgroupOf M
      rw [Subgroup.mem_subgroupOf]
      convert hq using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_inv_rev, inv_inv,
        mul_assoc]
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hmem
  exact hmem

end Steps

section Closed


theorem Smith23E1.smith23E1LgenCtx_holds : Smith23E1LgenCtxStatement := by
  have h34 := stroth34Statement_unconditional
  have h310 := stroth310Statement_unconditional
  have hNt := strothNtStatement_unconditional
  have h44 := stroth44Statement_unconditional
  have hW := CFSG.Walter.walter_modelsForm_of_lemma65_base CFSG.Walter.W67.lemma_6_5
    CFSG.Walter.Ree.T2.baseExists
  have hWL := KFacts.walterListLargeSylow_holds
  have hA2 := caseA2_closed (corollaryBStmt_of_theoremAStmt theoremAStmt_holds) h34 h310 hNt h44
  have hN := e1Natural_of_nt h34 h310 hNt
  have hS1 := step1_of h34 hN parabolic_holds
  have hC := ntCentral_of hNt hN hS1 parabolic_holds
  have hT := tMemNt_of hC hN omega4Basic_holds
  have hSplit := rtSplit_of h34 hNt hN hC hT omega4Basic_holds
  have hNK := e1NaturalK_of hN hSplit hNt natIrred_holds
  have hLine := ntLine_of hNt hNK hS1 hC parabolic_holds natIrred_holds
  have hTI := ntTI_of hLine
  have hLC := lemmaC_of parabolic_holds natIrred_holds
  have hCt := ctStructure_of hNK hSplit ctNormalizes_of hLine hLC normalizerOmega_holds
  have hF := m1FittingTrivial_of h44
  have hR := theoremR_of hLC sl2Root_holds hSplit hNK hLine hCt hF
  have hB1 := b1_of hLine hTI hSplit hNK omegaLine_holds
  have hB2 := b2_of hCt hSplit hTI
  have hTri := triple_of_free h1Tensor_holds sp4Involution_holds hNK hLine hCt hSplit hLC hS1
  have hD := caseBData_of_steps hB1 hB2 hTri
  have hB6 := b6_of hD hCt hSplit (ntConjLB_of hSplit) hB1 hB2 hTri
  have hB := caseBFalse_of_steps hD hB6 (b7a_of hB6) (b7b_of hB1 hB6 hTri hSplit) b7c_of
    (b8_of hW hWL hF hSplit hB6 (b7a_of hB6))
  have hA1 := caseA1_of hNK hCt hSplit hLine hTI dicksonNat_holds dicksonSpace_holds
  have hAb := CaseASylowAb.caseASylowAbelian_of hA2 ctNormalizes_of hSplit hLine hNK
    natIrred_holds dicksonNat_holds normalizerOmega_holds omega4Basic_holds
  have hA3 := caseA3_of hA2 listNoPerfectOut_holds hCt hSplit (caseASylow_of hA1 hLine) hAb hW hWL
    hC (ntElemAbelian_of hLine)
  have hP1 := xNormal_of (ntConjLB_of hSplit) hB hA3 (caseA4_of hCt hSplit hT)
  exact smith23E1LgenCtx_of_steps hSplit hR hP1

theorem stroth4i_holds : Stroth4iStatement := by
  intro G _ _ M Q Z B hc n t hS hCi
  have hcent := centTrivial_of_34_44 stroth34Statement_unconditional
    stroth44Statement_unconditional hc hS.width hS.n_gt hS.noA2 hS.gen
  have h := Smith23E1.smith23E1LgenCtx_holds G M Q Z B t hc hS.mem hS.notQ hcent hS.noA2 hS.gen
  obtain ⟨hQ, hNt, hR⟩ := hCi
  refine ⟨2, le_rfl, hQ, hNt, ?_⟩
  rcases hR with hp | hm
  · exact Or.inl ⟨hp, h.1 ⟨hQ, hNt, hp⟩⟩
  · exact Or.inr ⟨hm, h.2 ⟨hQ, hNt, hm⟩⟩

end Closed

end CFSG.RankThree.GF2n.Smith81
