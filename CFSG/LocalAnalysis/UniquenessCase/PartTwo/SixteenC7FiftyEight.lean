module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3Wr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_seven_fix {M V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) (hrank : 3 ≤ CFSG.Open.pRank 7 M)
    (hT : (tensorPairModel SL32 SL32).RealizesMod (barSub V₀ V hV L))
    (hnorm : Mbar M V₀ V hV ≤
      normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) :
    ∃ B : Subgroup G, B ≤ M ∧ IsPGroup 7 B ∧ ¬ IsCyclic B ∧
      3 ≤ rk ↥(fixV (barSub V₀ V hV B)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (by norm_num : Nat.Prime 7) hrank
  have hEst : E ≤ stabTil V₀ V := hEM.trans hMs
  have hEbel : IsElemAbelian 7 (barSub V₀ V hV E) :=
    (hEel.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
  have hEbN : barSub V₀ V hV E ≤
      normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hEM).trans hnorm
  obtain ⟨Q, hQE, hcard, hfix⟩ := exists_sub_of_isPGroup_seven hT hEbN hEbel.isPGroup
  have hid := s16c7_card_mul_card_preBarSub hV hEst hQE
  have hBE : preBarSub E V₀ V hV Q ≤ E := inf_le_left
  have hB49 : 49 ≤ Nat.card (preBarSub E V₀ V hV Q) := by
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    rw [hEcard] at hid
    by_contra hlt
    have hle : Nat.card (preBarSub E V₀ V hV Q) ≤ 48 := by omega
    nlinarith [Nat.mul_le_mul hle hcard]
  have hBel : IsElemAbelian 7 (preBarSub E V₀ V hV Q) := hEel.mono hBE
  have hbar : barSub V₀ V hV (preBarSub E V₀ V hV Q) = Q := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hQE
  refine ⟨preBarSub E V₀ V hV Q, hBE.trans hEM, hBel.isPGroup, ?_, ?_⟩
  · refine s16c7_not_isCyclic_of_elemAbelian (by norm_num) hBel ?_
    omega
  · rw [hbar]
    have hsq := s15_Infra_vtil_sq_eq_one V₀ V hV
    have h8 : Nat.card ↥(fixV Q) = 2 ^ rk ↥(fixV Q) := card_eq_two_pow hsq (fixV Q)
    rw [h8] at hfix
    by_contra hlt
    have : rk ↥(fixV Q) ≤ 2 := by omega
    have : 2 ^ rk ↥(fixV Q) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega

theorem r16_58_r_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) : R16_58_r D := by
  intro V₀ V L hV hS h7
  obtain ⟨K, _, hfin, hK, hmodel⟩ := h7.2.1
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hT := tensorNat_realizes_zmod_two hK2 hmodel
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hnorm := Mbar_le_normalizer_lBar_of_tensor D hV hS.setting.hyp151 hS.ne_bot hT
  have hsig : D.sig = {7} := h7.2.2
  have h7s : 7 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨B, hBM, hBp, hBc, hB3⟩ :=
    exists_noncyclic_seven_fix hV hMs (hx.three_le 7 h7s) hT hnorm
  have hBst : B ≤ stabTil V₀ V := hBM.trans hMs
  have hBV₀ : B ≤ centralizer (V₀ : Set G) :=
    le_centralizer_of_mSub_le_two (by norm_num) (by norm_num) hP.elemAbelian₀
      hS.setting.hyp16.small hBp (hBst.trans (stabTil_le_normalizer₀ V₀ V))
  have hV₀B : V₀ ≤ centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hBV₀ hb) v hv).symm
  have h1 := rk_add_rk_fixV_barSub_le hV hP.le (by norm_num : Nat.Prime 7) (by norm_num) hBp
    hBst hV₀B
  have h2 := rk_inf_centralizer_le_rMV D h61 h7s hBM hBp hBc hV
  have h3 : mSub V₀ + 3 ≤ rk ↥(V ⊓ centralizer (B : Set G)) := by
    have h4 : mSub V₀ = rk ↥V₀ := rfl
    omega
  exact le_trans (by exact_mod_cast h3) h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
