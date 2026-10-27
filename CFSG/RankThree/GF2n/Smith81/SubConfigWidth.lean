module

public import CFSG.RankThree.GF2n.Smith81.SubConfigSetup
public import CFSG.RankThree.GF2n.Smith81.SubConfigArith
import CFSG.RankThree.GF2n.Smith81.OrthTensorModel
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.SubCfg

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G]

theorem pow_two_mul_sub_one_dvd_card_omegaPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    {m i : ℕ} (hm : 3 ≤ m) (hi1 : 1 ≤ i) (him : i ≤ m - 1) :
    Nat.card K ^ (2 * i) - 1 ∣ Nat.card ↥(StatedOmega (StatedQuadPlus m K)) := by
  have h := card_statedOmega_plus_eq (K := K) hm
  have hdvd : ((Nat.card K ^ (2 * i) - 1 : ℕ) : ℤ) ∣
      (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) := by
    rw [h, Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos)]
    push_cast
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun i => ((Nat.card K : ℤ) ^ (2 * i) - 1))
      (Finset.mem_Icc.mpr ⟨hi1, him⟩)) _
  exact Int.natCast_dvd_natCast.mp hdvd

theorem strothConclusion_cases_of_card {M Q Z B : Subgroup G} {k : ℕ} (h4 : 4 ≤ Nat.card Z)
    (hk : Nat.card Q = Nat.card Z ^ k) (hk3 : k ≠ 3) (hk5 : k ≠ 5) (hk9 : k ≠ 9) (hk21 : k ≠ 21)
    (hk57 : k ≠ 57) (hC : StrothConclusion M Q Z B) :
    ¬ IsTIMod M Q (LB M Q B) ∧
      ((NoA2All M Q Z ∧ ∃ t ∈ LB M Q B, t ∉ Q ∧ CentTrivial M Q Z (Lgen M (LB M Q B)) ∧
        (StrothCii M Q Z B t ∨ StrothCiv M Q Z B t)) ∨ CaseVI M Q Z (Lgen M (LB M Q B))) := by
  have hinj : ∀ c, Nat.card Q = Nat.card Z ^ c → k = c := fun c hc =>
    Nat.pow_right_injective (by omega : 2 ≤ Nat.card Z) (hk.symm.trans hc)
  obtain ⟨hC, -⟩ := hC
  rcases hC with ⟨n, hq, ⟨e⟩⟩ | ⟨h5, -⟩ | ⟨h9, -⟩ | ⟨hTI, hrest⟩
  · exfalso
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [hq] at h4
      norm_num at h4
    have h3 : Nat.card Q = Nat.card Z ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 n hn0, hq]
    exact hk3 (hinj 3 h3)
  · exact absurd (hinj 5 h5) hk5
  · exact absurd (hinj 9 h9) hk9
  · refine ⟨hTI, ?_⟩
    rcases hrest with ⟨hNA, t, ht, htQ, hCT, hcase⟩ | h6
    · refine Or.inl ⟨hNA, t, ht, htQ, hCT, ?_⟩
      rcases hcase with ⟨h9, -⟩ | hii | ⟨h21, -⟩ | hiv | ⟨h57, -⟩
      · exact absurd (hinj 9 h9) hk9
      · exact Or.inl hii
      · exact absurd (hinj 21 h21) hk21
      · exact Or.inr hiv
      · exact absurd (hinj 57 h57) hk57
    · exact Or.inr h6

section Width

variable [Finite G] {M Q Z B : Subgroup G} {t : G}
  [(Q.subgroupOf (H0 M Z)).Normal]

theorem card_subCfgQ_of (hc : Ctx M Q Z B) {w : ℕ}
    (hN : Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ^ w) :
    Q ≤ Nt M (LB M Q B) t ∧ Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) = Nat.card Z ^ w := by
  have h1N : 1 < Nat.card (Nt M (LB M Q B) t) := by
    rw [hN]
    have hQ : 4 ≤ Nat.card Q := hc.hyp.q4.trans (Subgroup.card_le_of_le hc.hyp.Z_normal.1)
    have hZ : 1 ≤ Nat.card Z ^ w := Nat.one_le_pow _ _ Nat.card_pos
    nlinarith
  have hQN := Q_le_Nt_of_one_lt hc h1N
  refine ⟨hQN, ?_⟩
  have h := bar_card_mul_card_of_le (M := H0 M Z) hQN (Nt_le_H0 hc t)
  rw [hN, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem subConfig_width_E4 (hc : Ctx M Q Z B) (h4 : CaseE4 M Q Z B t)
    (hH' : StrothHyp (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    (hF : FrobClause (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t))) :
    Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) = Nat.card Z ^ 17 ∧
      ∃ d : ℕ, Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) =
        Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) ^ (d + 1) ∧ 17 ∣ d + 1 := by
  obtain ⟨-, hN17, hR, -⟩ := h4
  obtain ⟨f, -, hf, -⟩ := hc.hyp.cp
  have hf2 : 2 ≤ f := by
    have h4 := hc.hyp.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  obtain ⟨hQN, hQ'⟩ := card_subCfgQ_of hc hN17
  refine ⟨hQ', ?_⟩
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := hR
  haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans hf)
  have hX := CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) (n := 4)
    (by norm_num)
  obtain ⟨d, hd, hdvd⟩ := exists_card_quot_dvd_GL hc t hQN hH' hF hX e
  refine ⟨d, hd, ?_⟩
  obtain ⟨g, -, hg, -⟩ := hH'.cp
  have hcard := Nat.card_congr e.toEquiv
  have h6 := pow_two_mul_sub_one_dvd_card_omegaPlus (K := K) (m := 4) (i := 3) (by norm_num)
    (by norm_num) (by norm_num)
  rw [hK, hf] at h6
  refine e4_seventeen_dvd (g := g) hf2 ?_ h6 ?_
  · rw [← hg, ← hd, hQ', hf]
  · rw [← hcard, ← hg]
    exact hdvd

theorem subConfig_width_E5 (hc : Ctx M Q Z B) (h5 : CaseE5 M Q Z B t)
    (hH' : StrothHyp (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    (hF : FrobClause (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t))) :
    Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) = Nat.card Z ^ 33 ∧
      ∃ d : ℕ, Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) =
        Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) ^ (d + 1) ∧ 11 ∣ d + 1 := by
  obtain ⟨-, hN33, hR, -⟩ := h5
  obtain ⟨f, -, hf, -⟩ := hc.hyp.cp
  have hf2 : 2 ≤ f := by
    have h4 := hc.hyp.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  obtain ⟨hQN, hQ'⟩ := card_subCfgQ_of hc hN33
  refine ⟨hQ', ?_⟩
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := hR
  haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans hf)
  have hX := CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) (n := 6)
    (by norm_num)
  obtain ⟨d, hd, hdvd⟩ := exists_card_quot_dvd_GL hc t hQN hH' hF hX e
  refine ⟨d, hd, ?_⟩
  obtain ⟨g, -, hg, -⟩ := hH'.cp
  have hcard := Nat.card_congr e.toEquiv
  have h10 := pow_two_mul_sub_one_dvd_card_omegaPlus (K := K) (m := 6) (i := 5) (by norm_num)
    (by norm_num) (by norm_num)
  rw [hK, hf] at h10
  refine e5_eleven_dvd (g := g) hf2 ?_ h10 ?_
  · rw [← hg, ← hd, hQ', hf]
  · rw [← hcard, ← hg]
    exact hdvd

end Width

end CFSG.RankThree.GF2n.Smith81.SubCfg
