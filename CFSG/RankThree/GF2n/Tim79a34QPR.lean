module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusSixteenZQFour
public import CFSG.RankThree.GF2n.Tim79a34QEOutRed
public import CFSG.RankThree.GF2n.Tim79a34QPConfig
public import CFSG.RankThree.GF2n.Tim79a34StrothSimple
public import CFSG.RankThree.GF2n.Tim79a34CaseV
public import CFSG.RankThree.GF2n.Tim79a34CaseVIIIHolds

import CFSG.RankThree.GF2n.Stroth78.Sec3Single
import CFSG.RankThree.GF2n.Tim79a34QPDerived
import CFSG.RankThree.GF2n.Tim79a34QPSec4

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin
open CFSG.LargeExtraspecial.Timmesfeld (Qa)

theorem ntQP_false_of_steps_47 (hCfg : QPCfgExistsStatement) (hH : NTStrothHypStatement)
    (hS : NTStrothSimpleStatement) (h5 : NTCaseVStatement) (h8 : NTCaseVIIIStatement)
    (hSec4 : QPCfgSec4SetupStatement) (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (h47 : ∀ (G : Type) [Group G] [Finite G] (z : G) (E F : Subgroup G)
      (S : Stroth78.Setting z E F) (a : G) (w : ℕ) (h : Stroth78.Sec3Hyp S a w),
      (∀ Y : Subgroup (Stroth78.Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
        (∀ P : Subgroup (Stroth78.Hbar z), P ≤ Y → IsPGroup 2 P →
          Y ≤ Subgroup.normalizer (P : Set (Stroth78.Hbar z)) → P = ⊥) →
        (∀ y ∈ Y, ∀ r ∈ Stroth78.Rbar S a, y * r = r * y) →
        (∀ y ∈ Y, ∀ r ∈ Stroth78.Rbar S a,
          ∀ v ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace (Stroth78.rhoLin S r),
            Stroth78.rhoLin S y v = v) →
        Stroth78.aVec S h.mem_Q ∉
          (⨆ y ∈ Y, CFSG.RankThree.OrthogonalInvolutions.commSpace (Stroth78.rhoLin S y)) →
        Stroth78.Lbar S a ≤ Subgroup.normalizer (Y : Set (Stroth78.Hbar z)) →
        Stroth78.Rbar S a = ⊥ ∨ Y = ⊥) →
      (∀ α ∈ Stroth78.Eset S a, ∀ α' ∈ Stroth78.Eset S a, orderOf (α * α') ≤ 3) →
      StrothCaseV z w ∨ StrothCaseVI z w ∨ StrothCaseVIII z w)
    (hParrott : ParrottFi22Statement) (hO : OMinusSixTwoAutPSp43Statement)
    (hFi : Fi22InvolutionCentralizerStatement)
    (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hhyp : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H))
    (hQP : Q ≤ P) : False := by
  obtain ⟨n, Φ, ψ, a, T, ⟨cfg⟩⟩ := hCfg G M V Q P H hhyp hZ hn hQP
  obtain ⟨E, F, w, hyp, hw, hcard⟩ := hH G M V Q P H Φ ψ a T cfg
  obtain ⟨n1, -, -, -, n6, -⟩ := hS G M V Q P H Φ ψ a T cfg w hw
  have h5' := h5 hParrott hO hFi G M V Q P H Φ ψ a T cfg w hw
  have h8' := h8 G M V Q P H Φ ψ a T cfg w hw
  obtain ⟨h212, b, hbQ, hbZ, hbconj, hba⟩ := hSec4 G M V Q P H Φ ψ a T cfg
  have hn3 := cfg.three
  have h3w : 3 ≤ w := by omega
  have hw4 : 4 ≤ w := by omega
  let S : Stroth78.Setting cfg.aG E F := Stroth78.Setting.ofHyp hyp
  have hS3 : Stroth78.Sec3Hyp S b w := ⟨hcard, h3w, n1, h212, hbQ, hbZ, hbconj, hba⟩
  have hZV : Stroth78.ZQ cfg.aG = V := by
    show centerIn (Qa cfg.aG) = V
    rw [qa_aG_eq h12 cfg, centerIn_Q_eq h11b cfg]
  have hZ4 : Nat.card ↥(Stroth78.ZQ cfg.aG) = 4 := card_centerIn_qa h11b h12 cfg
  rcases Stroth78.threeFourPlus_or_orderOf_le_three S b
    (fun α hα α' hα' => Stroth78.orderOf_mul_le_four_of_mem_Eset S b hα hα') with h34 | h3
  · refine Stroth78.false_of_threeFourPlus_of_card_ZQ_eq_four S hS3 h34 hw4 hZ4 ?_
    have hV4 : Nat.card ↥V = 4 := qpCfg_card_V cfg
    have hord : Nat.card ↥(Subgroup.zpowers cfg.aG) = 2 := by
      rw [Nat.card_zpowers]
      exact qpCfg_orderOf_aG cfg
    have hnle : ¬ V ≤ Subgroup.zpowers cfg.aG := fun hle => by
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨x, hxV, hxz⟩ := SetLike.not_le_iff_exists.mp hnle
    exact ⟨x, by rw [hZV]; exact hxV, hxz, qpCfg_V_le_commutator cfg hxV⟩
  · have h217 := Stroth78.stroth78_217_of_card_ZQ_eq_four S hbQ hbconj hbZ hba hZ4
    rcases h47 G cfg.aG E F S b w hS3 h217 h3 with h | h | h
    · exact h5' h
    · exact n6 h
    · exact h8' h

theorem ntQP_false_of_47
    (h47 : ∀ (G : Type) [Group G] [Finite G] (z : G) (E F : Subgroup G)
      (S : Stroth78.Setting z E F) (a : G) (w : ℕ) (h : Stroth78.Sec3Hyp S a w),
      (∀ Y : Subgroup (Stroth78.Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
        (∀ P : Subgroup (Stroth78.Hbar z), P ≤ Y → IsPGroup 2 P →
          Y ≤ Subgroup.normalizer (P : Set (Stroth78.Hbar z)) → P = ⊥) →
        (∀ y ∈ Y, ∀ r ∈ Stroth78.Rbar S a, y * r = r * y) →
        (∀ y ∈ Y, ∀ r ∈ Stroth78.Rbar S a,
          ∀ v ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace (Stroth78.rhoLin S r),
            Stroth78.rhoLin S y v = v) →
        Stroth78.aVec S h.mem_Q ∉
          (⨆ y ∈ Y, CFSG.RankThree.OrthogonalInvolutions.commSpace (Stroth78.rhoLin S y)) →
        Stroth78.Lbar S a ≤ Subgroup.normalizer (Y : Set (Stroth78.Hbar z)) →
        Stroth78.Rbar S a = ⊥ ∨ Y = ⊥) →
      (∀ α ∈ Stroth78.Eset S a, ∀ α' ∈ Stroth78.Eset S a, orderOf (α * α') ≤ 3) →
      StrothCaseV z w ∨ StrothCaseVI z w ∨ StrothCaseVIII z w)
    (hParrott : ParrottFi22Statement) (hO : OMinusSixTwoAutPSp43Statement)
    (hFi : Fi22InvolutionCentralizerStatement)
    (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H))
    (hQP : Q ≤ P) : False := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have hIW : Sec34IWStatement :=
    sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h11c : Lemma11cStatement := lemma11c_holds spRadFactsStatement_holds h11a
  have h12 : Lemma12Statement :=
    lemma12_holds hIW CFSG.RankThree.GF2n.Tim79a.Gamma.sec34GammaStatement_holds h11a h11b h11c
  have h13 : Lemma13Statement := lemma13_holds hN h11b h11c
  have hSH : NTStrothHypStatement := ntStrothHyp_holds h11a h11b h12
  exact ntQP_false_of_steps_47 (qPCfgExistsStatement_holds hN hIW) hSH
    (ntStrothSimple_holds h11a h11b h12 h13) (ntCaseV_holds hSH h11a h11b h12 h13)
    ntCaseVIIIStatement_holds (qpCfgSec4Setup_of hN hIW) h11b h12 h47 hParrott hO hFi G M V Q P H
    hH hZ hn hQP

theorem ntQEOut_false_of_47
    (h47 : ∀ (G : Type) [Group G] [Finite G] (z : G) (E F : Subgroup G)
      (S : Stroth78.Setting z E F) (a : G) (w : ℕ) (h : Stroth78.Sec3Hyp S a w),
      (∀ Y : Subgroup (Stroth78.Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
        (∀ P : Subgroup (Stroth78.Hbar z), P ≤ Y → IsPGroup 2 P →
          Y ≤ Subgroup.normalizer (P : Set (Stroth78.Hbar z)) → P = ⊥) →
        (∀ y ∈ Y, ∀ r ∈ Stroth78.Rbar S a, y * r = r * y) →
        (∀ y ∈ Y, ∀ r ∈ Stroth78.Rbar S a,
          ∀ v ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace (Stroth78.rhoLin S r),
            Stroth78.rhoLin S y v = v) →
        Stroth78.aVec S h.mem_Q ∉
          (⨆ y ∈ Y, CFSG.RankThree.OrthogonalInvolutions.commSpace (Stroth78.rhoLin S y)) →
        Stroth78.Lbar S a ≤ Subgroup.normalizer (Y : Set (Stroth78.Hbar z)) →
        Stroth78.Rbar S a = ⊥ ∨ Y = ⊥) →
      (∀ α ∈ Stroth78.Eset S a, ∀ α' ∈ Stroth78.Eset S a, orderOf (α * α') ≤ 3) →
      StrothCaseV z w ∨ StrothCaseVI z w ∨ StrothCaseVIII z w)
    (hParrott : ParrottFi22Statement) (hO : OMinusSixTwoAutPSp43Statement)
    (hFi : Fi22InvolutionCentralizerStatement) (hR : NTQEOutResidualStatement)
    (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H))
    (hrel : P.relIndex Q = 2)
    (hN : ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) : False := by
  obtain ⟨M₀, V₀, H₀, hH₀, hZ₀, hn₀⟩ := hR G M V Q P H hH hZ hn hrel hN
  exact ntQP_false_of_47 h47 hParrott hO hFi _ M₀ V₀ _ _ H₀ hH₀ hZ₀ hn₀ le_rfl

end CFSG.RankThree.GF2n.Tim79a
