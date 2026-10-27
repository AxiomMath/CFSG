module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_not_le_M_of_choice (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV)
    (hm : 1 < mBar D.M V₀ V hV) (h0 : V₀ = ⊥)
    (h1 : Case168_9 D V₀ V hV L → v1Sub D.M V₀ V hV L = ⊥) {A : Subgroup G}
    (hA : Choice1613 D V₀ V hV L A) {g : G} (hAg : A ≤ conjSubgroup V g) :
    ¬ conjSubgroup V g ≤ D.M := by
  intro hVgM
  have hP := hc.setting.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hVgst : conjSubgroup V g ≤ stabTil V₀ V := hVgM.trans hMst
  have hVel : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hs : 1 < E3.sParam hV := by
    subst h0
    exact s16c167_one_lt_sParam D hx h61 hc.setting.hyp16.hyp125 hm
  by_cases hbot : barSub V₀ V hV (conjSubgroup V g) = ⊥
  · have hAb : barSub V₀ V hV A = ⊥ := le_bot_iff.1 (hbot ▸ barSub_mono V₀ V hV hAg)
    rcases hA.2 with hcomm | ⟨-, hnst⟩
    · exact hcomm (by rw [hAb, Subgroup.commutator_bot_right])
    · exact hnst (by rw [hAb]; exact bot_le)
  · have hhyp : ∀ B : Subgroup G, B ≤ conjSubgroup V g → E3.mQuot (conjSubgroup V g) B < 2 →
        V ⊓ centralizer (B : Set G) =
          V ⊓ centralizer ((conjSubgroup V g : Subgroup G) : Set G) := by
      intro B hBA hlt
      have hlt' : E3.mQuot (conjSubgroup V g) B < E3.sParam hVel := by
        rw [E3.sParam_conj hV g hVel]; omega
      exact (E3.e3_6 hVel hBA le_rfl hlt' (B2F.isPGroup_of_isElemAbelian hV)).1.symm
    have hmem : barSub V₀ V hV (conjSubgroup V g) ∈ calABar 2 D.M V₀ V hV :=
      s16c167_barSub_mem_calABar_of_le hV h0 hVgM hVgst hVel hbot hhyp
    rcases hA.2 with hcomm | ⟨hc9, hnst⟩
    · have hXodd : Odd (Nat.card (oddBar D.M V₀ V hV)) :=
        Nat.coprime_two_left.mp (coprime_card_relPPrimeCore Nat.prime_two (Mbar D.M V₀ V hV))
      have hMbarNorm : Mbar D.M V₀ V hV ≤
          normalizer (oddBar D.M V₀ V hV : Set (MulAut (Vtil V₀ V hV))) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (relPPrimeCore_le (Mbar D.M V₀ V hV))).1
          (relPPrimeCore_normal Nat.prime_two (Mbar D.M V₀ V hV))
      have hcomm0 : ⁅oddBar D.M V₀ V hV, barSub V₀ V hV (conjSubgroup V g)⁆ = ⊥ :=
        thin_four_twentySix_commutator_eq_bot (s15_Infra_vtil_sq_eq_one V₀ V hV) hmem hXodd
          ((barSub_mono V₀ V hV hVgM).trans hMbarNorm)
      exact hcomm (le_bot_iff.1
        ((Subgroup.commutator_mono le_rfl (barSub_mono V₀ V hV hAg)).trans hcomm0.le))
    · have h1' := h1 hc9
      have hst' : conjSubgroup V g ≤ stabTil (v1Sub D.M V₀ V hV L) V := by
        rw [h1']; exact h0 ▸ hVgst
      have hbot' : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup V g) ≠ ⊥ := by
        rw [h1']; exact h0 ▸ hbot
      have hbar : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup V g) ∈
          calABar 2 D.M (v1Sub D.M V₀ V hV L) V hV :=
        s16c167_barSub_mem_calABar_of_le hV h1' hVgM hst' hVel hbot' hhyp
      have hpre := fifteen_seven D hc.setting.hyp151 hV hbar
      have hVgW : conjSubgroup V g ≤ normalizer (wSub V₀ V hV L : Set G) :=
        (le_preBarSub_barSub hV hVgM hst').trans hpre
      exact hnst ((barSub_mono V₀ V hV hAg).trans
        (s16c167_barSub_le_stabSub_wTil hV hVgst hVgW))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
