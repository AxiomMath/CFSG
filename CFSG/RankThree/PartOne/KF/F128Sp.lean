module

public import CFSG.RankThree.PartOne.KF.F128Cls
public import CFSG.RankThree.PartOne.KF.F122Sp
public import CFSG.RankThree.PartOne.KF.ClsPSp
public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.KFU
open CFSG.RankThree.PartOne.K1214 (SylowShape)

theorem kf128SylTag_PSp
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF128SylTag .PSp := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hkerp hLR2 n f₀ hf₀ hM α hαp hαinn hLRA hX hF hrk
  classical
  have hp2 : p ≠ 2 := by omega
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hcl : StatedClassicalModel T .PSp n 2 (p * f₀) :=
    K1214.statedClassicalModel_of_lieModel_of_tag' (Or.inr (Or.inl rfl)) hM
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := id hcl
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
  have hm : Models.LieModel T .PSp n 2 (p * f₀) := ⟨hadm, Or.inl hcl⟩
  have hT0 : Subgroup.center T = ⊥ := center_eq_bot_of_cover hq.1 π hπ hcl
  have hdvd := card_ker_dvd_multiplier_cls hq π hπ hker hGA hm
  have hZodd : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card π.ker := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (card_multiplier_psp_dvd_two (n := n) (by omega))
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  have hle3 : ∀ r : ℕ, r.Prime → r ≠ 2 → localRank r T ≤ 3 := fun r hr hr2 =>
    localRank_le_three_of_cover π hπ he hr hr2 (hZodd r hr hr2)
  have hlr : ∀ r : ℕ, r.Prime → localRank r T = localRank r (StatedProj (StatedSp n K)) :=
    fun r hr => CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]; intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow h))
  have hrank1 : 3 ≤ orderOf (Nat.card K : ZMod p) → n ≤ 3 → CFSG.pRank p T ≤ 1 := by
    intro hd3 hn3
    have hε : T ≃* ↥(StatedSp n K) := e.trans (spEquivProj (by omega)).symm
    rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt hε]
    refine pRank_statedSp_le_one hp hp2 hpK ?_
    have hd0 : 0 < orderOf (Nat.card K : ZMod p) := by omega
    split_ifs with hev
    · refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd0).2 ?_)
      obtain ⟨k, hk⟩ := hev
      omega
    · refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd0).2 ?_)
      omega
  by_cases hn4 : 4 ≤ n
  ·
    exfalso
    obtain ⟨r, hr, hr2, -, hrd⟩ :=
      exists_odd_prime_dvd_two_pow_sub_one_ne_five (f := p * f₀) (by omega)
    have hrK : r ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hrd
    have h4 := le_localRank_statedSp_torus (K := K) hr hr2 hrK (by omega : 1 ≤ n)
    have h3 := hle3 r hr hr2
    rw [hlr r hr] at h3
    omega
  · have hn : n = 2 ∨ n = 3 := by omega
    by_cases hpq : p ∣ 2 ^ (p * f₀) - 1
    ·
      exfalso
      rcases hn with rfl | rfl
      · exact false_of_row kf122Row7_holds hp hp5 hT0
          ⟨p * f₀, by omega, hpq, statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp
          hαinn hLRA
      · have hrK : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hpq
        have h3 := le_localRank_statedSp_torus (K := K) hp hp2 hrK (by omega : 1 ≤ 3)
        rw [← hlr p hp] at h3
        exact false_of_three_le_localRank hp hLR2 h3
    · by_cases hpq' : p ∣ 2 ^ (p * f₀) + 1
      · rcases hn with rfl | rfl
        ·
          have hpg : p ∣ 2 ^ f₀ + 1 := dvd_two_pow_add_one_of_mul hp hpq'
          obtain ⟨e', m, m', he2, hm', hm'p, hmm, hmp⟩ := K1214.lte_plus hp hp2 hpg
          refine ⟨e', he2, ?_, ?_⟩
          · exact K1214.sylowShape_of_psp4Model hp hp2 (by omega) hmm hmp hcl
          · have hXc : Blueprint.LieModel
                (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .PSp 2 2 f₀ := by
              rcases hX with hX | ⟨ht, -⟩
              · exact hX
              · exact absurd ht (by decide)
            have hclN := K1214.statedClassicalModel_of_lieModel_of_tag' (Or.inr (Or.inl rfl)) hXc
            have hmN : Models.LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .PSp 2 2 f₀ :=
              ⟨hclN.1, Or.inl hclN⟩
            have hNZ : ¬ p ∣ Nat.card (Subgroup.center ↥(fixRes α)) := by
              intro hd
              have h2 := (hd.trans (card_center_fixRes_dvd α hGA hmN)).trans
                (card_multiplier_psp_dvd_two (n := 2) hf₀)
              exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
            exact sylowShape_of_center_quotient hp hNZ
              (K1214.sylowShape_of_psp4Model hp hp2 (by omega) hm' hm'p hclN)
        ·
          exfalso
          exact false_of_row kf122Row10_holds hp hp5 hT0
            ⟨p * f₀, by omega, hpq', statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp
            hαinn hLRA
      ·
        exfalso
        have hq1 : 1 ≤ Nat.card K := Nat.card_pos
        have hd3 : 3 ≤ orderOf (Nat.card K : ZMod p) := by
          refine three_le_orderOf_of_not_dvd hp hpK ?_ ?_ hq1
          · rw [hK]; exact hpq
          · rw [hK]; exact hpq'
        have := hrank1 hd3 (by omega)
        omega

end CFSG.RankThree.PartOne
