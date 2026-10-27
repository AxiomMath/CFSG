module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Hyper
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLemmaP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sixteen_seven2_hyperplane_exists' (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥)
    (h1 : Case168_9 D V₀ V hV L → v1Sub D.M V₀ V hV L = ⊥) {A : Subgroup G}
    (hA : Choice1613 D V₀ V hV L A) : ∃ B U : Subgroup G, Hyperplane1618 V A B U := by
  have hP := h.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨hAT, g, hAg, -⟩ := hA.1
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAst : A ≤ stabTil V₀ V := hAM.trans hMst
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  by_contra hno
  have hhyp : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B = 1 →
      V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G) := by
    intro B hBA hm
    by_contra hne
    exact hno ⟨B, V ⊓ centralizer (B : Set G), hBA, hm, rfl, hne⟩
  rcases hA.2 with hc | ⟨h9, hc⟩
  · have hA1 : barSub V₀ V hV A ≠ ⊥ := by
      intro hbot
      exact hc (by rw [hbot, Subgroup.commutator_bot_right])
    have hAmem : barSub V₀ V hV A ∈ E3.aSet 2 (Mbar D.M V₀ V hV) :=
      s16c167_barSub_mem_calABar_of_hyperplanes hV h0 hAM hAst hAel hA1 hhyp
    have hXodd : Odd (Nat.card (oddBar D.M V₀ V hV)) :=
      Nat.coprime_two_left.mp (coprime_card_relPPrimeCore Nat.prime_two (Mbar D.M V₀ V hV))
    have hMbarNorm : Mbar D.M V₀ V hV ≤
        normalizer (oddBar D.M V₀ V hV : Set (MulAut (Vtil V₀ V hV))) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (relPPrimeCore_le (Mbar D.M V₀ V hV))).1
        (relPPrimeCore_normal Nat.prime_two (Mbar D.M V₀ V hV))
    have hcomm : ⁅oddBar D.M V₀ V hV, barSub V₀ V hV A⁆ = ⊥ :=
      thin_four_twentySix_commutator_eq_bot (s15_Infra_vtil_sq_eq_one V₀ V hV) hAmem hXodd
        ((barSub_mono V₀ V hV hAM).trans hMbarNorm)
    exact absurd hcomm hc
  · have h1' := h1 h9
    have hA1 : barSub V₀ V hV A ≠ ⊥ := by
      intro hbot
      exact hc (by rw [hbot]; exact bot_le)
    have hAst' : A ≤ stabTil (v1Sub D.M V₀ V hV L) V := by
      rw [h1']
      exact h0 ▸ hAst
    have hA1' : barSub (v1Sub D.M V₀ V hV L) V hV A ≠ ⊥ := by
      rw [h1']
      exact h0 ▸ hA1
    have hAbar : barSub (v1Sub D.M V₀ V hV L) V hV A ∈
        calABar 2 D.M (v1Sub D.M V₀ V hV L) V hV :=
      s16c167_barSub_mem_calABar_of_hyperplanes hV h1' hAM hAst' hAel hA1' hhyp
    have hpre := fifteen_seven D h.hyp151 hV hAbar
    have hA_norm : A ≤ normalizer (wSub V₀ V hV L : Set G) :=
      (le_preBarSub_barSub hV hAM hAst').trans hpre
    exact absurd (s16c167_barSub_le_stabSub_wTil hV hAst hA_norm) hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
