module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec12Omega6PlusStepBRed
public import CFSG.RankThree.GF2n.Smith81.ERecursion
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec12Omega6PlusTruth

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def SmithE6FourClauseBelow (N : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < N →
  ∀ (M Q Z B : Subgroup X) (hc : Ctx M Q Z B),
    StrothConclusion M Q Z B → ¬ IsTIMod M Q (LB M Q B) →
    CFSG.RankThree.GF2n.Smith81.CaseE6 M Q Z B 4 →
      IsPSLModel 6 (Nat.card Z) ↥(generalizedFitting X)

theorem SmithE6FourClauseBelow_of_smith1981 {N : ℕ}
    (h : CFSG.RankThree.GF2n.Smith81.Smith1981TheoremBelow N) :
    SmithE6FourClauseBelow N := by
  intro X _ _ hX M Q Z B hc hConcl hnTI hE6
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlast⟩ :=
    h X hX M Q Z hc.hyp B hc.conj hc.le hc.ne hConcl
  obtain ⟨f, hf, hL, -⟩ := hlast hnTI 4 hE6
  obtain ⟨-, K, iF, iK, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
  exact ⟨K, iF, iK, hK.trans hf.symm, ⟨e⟩⟩

theorem stroth12Omega6PlusStepB_of_below {N : ℕ}
    (hSmith : SmithE6FourClauseBelow N) (hq : Sec12Omega6PlusQStatement) :
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < (N + 1) →
    ∀ (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
      (hc : Ctx M Q Z B) (n : ℕ), Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q →
      OmegaPlusNat hc t 3 → SubConfigSatz M Q Z (hc.CN t) →
      (∃ hN : (Q.subgroupOf (H0 M Z)).Normal, haveI := hN
        ∀ B₂ : Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)),
          Ctx (Subgroup.normalizer ((cen (bar (H0 M Z) Q (hc.CN t)) : Subgroup _) : Set _))
            (bar (H0 M Z) Q (hc.CN t)) (cen (bar (H0 M Z) Q (hc.CN t))) B₂ →
          SecondCfgCaseE6Four (bar (H0 M Z) Q (hc.CN t)) B₂) →
      FStarL6 M Q Z := by
  intro G _ _ hG M Q Z B hN hc n h12 t ht htQ hp hsub hE6
  obtain ⟨hNH, hall⟩ := hE6
  haveI := hNH
  obtain ⟨hNq, hSatz⟩ := ConfigSatz.of_subConfigSatz hsub
  obtain ⟨B₂, hcB₂, hConcl⟩ := ConfigSatz.exists_ctx hSatz
  have hSecond := hall B₂ hcB₂
  have hE6case := caseE6_of_secondCfgCaseE6Four hSecond
  have hHbar_lt : Nat.card (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) < Nat.card G :=
    CFSG.RankThree.GF2n.Smith81.card_H0_quot_lt hc.hyp
  have hGN : Nat.card G ≤ N := Nat.lt_succ_iff.mp hG
  have hbound : Nat.card (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) < N :=
    lt_of_lt_of_le hHbar_lt hGN
  have hPSL := hSmith _ hbound _ _ _ _ hcB₂ hConcl hSecond.1 hE6case
  have hq' := hq G M Q Z B hc n h12 t ht htQ hp hsub
  obtain ⟨hnb, hbE⟩ := quotMulEquivBar (M := M) hc.Q_le_H0' (fun _ hx => hx.1)
  obtain ⟨e⟩ := hbE
  have hmap := CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  have hF : ↥(generalizedFitting (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z))) ≃*
      ↥(generalizedFitting ↥(bar M Q (H0 M Z))) :=
    (MulEquiv.subgroupMap e (generalizedFitting _)).trans (MulEquiv.subgroupCongr hmap)
  have hPSL' : IsPSLModel 6 (Nat.card Z)
      ↥(generalizedFitting (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z))) := by
    rw [← hq']
    exact hPSL
  exact IsPSLModel.congr hF hPSL'

end CFSG.RankThree.GF2n.Stroth80
