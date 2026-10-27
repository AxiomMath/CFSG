module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s16c1610_zpow_apply_eq {W : Type*} [Group W] (y : MulAut W) (x : W)
    (h : y x = x) (k : ℤ) : (y ^ k) x = x := by
  have hy : y ∈ MulAction.stabilizer (MulAut W) x := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have := (MulAction.stabilizer (MulAut W) x).zpow_mem hy k
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

theorem s16c1610_false_of_isTensorS3L2 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (h16 : Hyp16 D V₀ V)
    (hσ : D.sig = {3}) {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (hm4 : m = 4 → 3 < CFSG.Open.evenRank G)
    (hT : IsTensorS3L2 (Vtil V₀ V hV) (Mbar D.M V₀ V hV) m) : False := by
  have h125 : Hyp125 D V₀ V := h16.hyp125
  have hpf := h125.pairFacts
  have hMn : D.M ≤ normalizer (V : Set G) := hpf.le_normalizer
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have h3σ : 3 ∈ D.sig := by
    rw [hσ]
    exact Set.mem_singleton 3
  have hc4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D h16
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  obtain ⟨-, -, -, hY⟩ := exists_rank_data h115 (Hyp125.hyp11 h127 h125) hc4 h3σ
  have hYker : ∀ Y : Subgroup ↥D.M, IsElemAbelian 3 Y → Y ≤ (barHom V₀ V hV hMst).ker →
      Nat.card Y ≤ 3 := fun Y hYel hYk =>
    hY Y hYel (by rwa [ker_barHom V₀ V hV hMn hMst] at hYk)
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp3 (H := D.M) (k := 3)
      (hx.three_le 3 h3σ)
  refine s16c1610_false_of_fix_noncyclic D h61 h127 (hV := hV) h16 hMst hp3 le_rfl h3σ hEM hEel
    hEcard ?_
  intro x hx1
  by_cases hm5' : m = 5
  · subst hm5'
    obtain ⟨F, hFG, hFel, hFcard, hFfix⟩ := s16c1610_tensor_exists_elemAbelian_nine_fix hT hx1
    obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_map_le (barHom V₀ V hV hMst) hp3
      (Eb := F) (by rw [range_barHom]; exact hFG) hFel.isPGroup
      (s16c1610_not_isCyclic_of_isElemAbelian hp3 hFel (by rw [hFcard]; norm_num))
    exact ⟨B, hBp, hBc, fun b hb => hFfix _ (hB b hb)⟩
  · have hm34 : m = 3 ∨ m = 4 := by omega
    obtain ⟨u, huG, hu3, hufix⟩ := s16c1610_tensor_exists_order_three_fix hm3 hT hx1
    have hmr : m ≤ CFSG.Open.pRank 3 D.M := by
      rcases hm34 with h | h
      · rw [h]
        exact hx.three_le 3 h3σ
      · rw [h]
        exact hx.four_le (hm4 h) 3 h3σ
    obtain ⟨Em, hEmel, hEmcard⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank hp3 hmr
    have hR : ¬ 3 ^ m ∣ Nat.card (barHom V₀ V hV hMst).range := by
      rw [range_barHom, (s16c1610_card_of_isTensorS3L2 hT).1]
      exact s16c1610_not_dvd_card_tensor hm3 (by omega)
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, by omega⟩
    obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_of_kernel_trick (barHom V₀ V hV hMst)
      hp3 hEmel hEmcard hR hYker (y := u) (by rw [range_barHom]; exact huG)
      (by rw [← hu3]; exact pow_orderOf_eq_one u)
      (by
        intro h
        rw [h, orderOf_one] at hu3
        omega)
    refine ⟨B, hBp, hBc, fun b hb => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hB b hb)
    rw [← hk]
    exact s16c1610_zpow_apply_eq u x hufix k

private theorem s16c1610_sumOfNat_congr_v1 {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (L : Subgroup G) {m : ℕ} {V₀ V₁ : Subgroup G} (h : V₁ = V₀)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (barSub V₁ V hV L)
      (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 2) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (barSub V₀ V hV L)
      (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2 := by
  subst h
  exact hsum

theorem s16c1610_out10_of_case2_ln (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3) (hσ : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hdir : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (hm4 : V₀ ≠ ⊥ → m = 4 → 3 < CFSG.Open.evenRank G)
    (hL₀ : IsLn ↥L₀ m 1) (hL : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) : Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hstar := s16c1610_rk_vStar_le (L := L) D h125
  have hrk : 2 * m ≤ rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) :=
    s16c1610_le_rk_sumOfNat_two (r := m) (fun I hI => by
      have := s16c1610_rk_binaryNaturalSL hI
      omega) hsum
  rw [rk_top] at hrk
  obtain ⟨X, hXM, hXcard, hXnorm⟩ := s16c1610_exists_normal_three_of_direct hK hdir
  have hk : D.k < mBar D.M V₀ V hV :=
    s16c1610_k_lt_mBar_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1214 h125 (Or.inl rfl)
      (s16c1610_k_lt_dParam_three D hin.hSg hin.h1219 (by rw [hσ]; simp)) hXM hXcard hXnorm
      (by
        rw [s16c1610_dParam_three]
        exact le_trans (by omega) (hrk.trans hstar))
  refine ⟨hk, fun hV₀ _ => ?_⟩
  exfalso
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (lBar V₀ V hV L)
      (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2 :=
    s16c1610_sumOfNat_congr_v1 hV L (v1Sub_of_ne_bot D.M V₀ V hV L hV₀) hsum
  have hcard : Nat.card (lBar V₀ V hV L) = Nat.card L₀ :=
    (SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL).trans
      (SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL₀).symm
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hLeq : lBar V₀ V hV L = L₀ :=
    s16c1610_eq_of_direct_of_centralizer rfl (barSub_mono V₀ V hV hc.setting.hyp151.le) hK hdir
      hcard
  rw [← hLeq] at hdir
  exact s16c1610_false_of_isTensorS3L2 D hin.hx hin.h61 hin.h127 hc.setting.hyp16 hσ hm3 hm5
    (hm4 hV₀) (s16c1610_isTensorS3L2_of_sum_natural hm3 hK hL hdir hsum')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
