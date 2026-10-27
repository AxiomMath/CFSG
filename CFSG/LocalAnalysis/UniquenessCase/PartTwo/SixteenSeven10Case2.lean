module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

private theorem s16c1610_factorial_bounds {n : ℕ} (h6 : 6 ≤ n) (h11 : n ≤ 11) :
    9 < Nat.factorial n ∧ Nat.factorial n < 2 ^ ((n - 2) * (n - 2) - 2) := by
  interval_cases n <;> decide

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16c1610_out10_of_case2_sym (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3) (hσ : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hdir : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    {n : ℕ} (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hS : IsSym ↥L₀ n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n) (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) : Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hcard : Nat.card L₀ = Nat.factorial n := s16c1610_card_of_isSym hS
  have hstar := s16c1610_rk_vStar_le (L := L) D h125
  obtain ⟨m₀, r₀, hm₀, hr₀, hrk₀, h9, hN⟩ : ∃ m₀ r₀ : ℕ, 4 ≤ m₀ ∧ 2 * m₀ ≤ r₀ + 1 ∧
      r₀ ≤ rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) ∧ 9 < Nat.factorial n ∧
      Nat.factorial n < 2 ^ (m₀ * m₀ - 2) := by
    by_cases h5 : n = 5
    · subst h5
      refine ⟨4, 8, le_rfl, by norm_num, ?_, by decide, by decide⟩
      have := s16c1610_le_rk_sumOfNat_two (r := 4) (fun I hI => by
        have := s16c1610_rk_alternatingNatural_odd (n := 5) (by decide) hI
        omega) hsum
      omega
    · have h6 : 6 ≤ n := by omega
      obtain ⟨h9, hN⟩ := s16c1610_factorial_bounds h6 hn11
      refine ⟨n - 2, 2 * (n - 2), by omega, by omega, ?_, h9, hN⟩
      exact s16c1610_le_rk_sumOfNat_two (r := n - 2)
        (fun I hI => s16c1610_le_rk_alternatingNatural (by omega) hI) hsum
  rw [rk_top] at hrk₀
  exact s16c1610_out10_of_case2_core D hin hc hK hσ hdir hm₀ hr₀ (hrk₀.trans hstar)
    (by rw [hcard]; exact h9) (by rw [hcard]; exact hN)

theorem s16c1610_out10_of_case2_sp (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3) (hσ : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hdir : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    (hS : IsSpn ↥L₀ 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1) (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) : Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hcard : Nat.card L₀ = 1451520 := s16c1610_card_of_isSpn_six hS
  have hstar := s16c1610_rk_vStar_le (L := L) D h125
  have hrk₀ : 2 * 6 ≤ rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) :=
    s16c1610_le_rk_sumOfNat_two (r := 6) (fun I hI => (s16c1610_rk_natSpn hI).ge) hsum
  rw [rk_top] at hrk₀
  exact s16c1610_out10_of_case2_core D hin hc hK hσ hdir (m₀ := 6) (r₀ := 12) (by norm_num)
    (by norm_num) (hrk₀.trans hstar) (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)

theorem s16c1610_out10_of_case2_ominus_six (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3) (hσ : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hdir : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    (hO : IsOMinus ↥L₀ 6 1) (hO' : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1) (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) : Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hcard : Nat.card L₀ = 51840 := s16c1610_card_of_isOMinus_six hO hO'
  have hstar := s16c1610_rk_vStar_le (L := L) D h125
  have hrk₀ : 2 * 6 ≤ rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) :=
    s16c1610_le_rk_sumOfNat_two (r := 6)
      (fun I hI => (s16c1610_rk_natOmegaMinus (by norm_num) hI).ge) hsum
  rw [rk_top] at hrk₀
  exact s16c1610_out10_of_case2_core D hin hc hK hσ hdir (m₀ := 6) (r₀ := 12) (by norm_num)
    (by norm_num) (hrk₀.trans hstar) (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)

theorem s16c1610_out10_of_case2_ominus_eight (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3) (hσ : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hdir : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    (hO : IsOMinus ↥L₀ 8 1) (hO' : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1) (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) : Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hcard : Nat.card L₀ = 394813440 := s16c1610_card_of_isOMinus_eight hO hO'
  have hstar := s16c1610_rk_vStar_le (L := L) D h125
  have hrk₀ : 2 * 8 ≤ rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) :=
    s16c1610_le_rk_sumOfNat_two (r := 8)
      (fun I hI => (s16c1610_rk_natOmegaMinus (by norm_num) hI).ge) hsum
  rw [rk_top] at hrk₀
  exact s16c1610_out10_of_case2_core D hin hc hK hσ hdir (m₀ := 8) (r₀ := 16) (by norm_num)
    (by norm_num) (hrk₀.trans hstar) (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
