module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4L52
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114SolvOver
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveStrong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankTwistedE6
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsModels
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwMain
import CFSG.Assembly.E6FourLabelArith
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_pRank_psl_of_five_le (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ}
    (hS : StatedClassicalModel (K ⧸ center K) .PSL m 2 n) (hm : 5 ≤ m) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkLin m true (2 ^ n) r (Nat.card (center K)) := by
  obtain ⟨q, hv, hqp, hqc, ⟨e⟩⟩ := uc22p20w_index_psl hS (by
    rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega)
  rw [hT K hq ⟨.A (m - 1) q, hv⟩ hqp ⟨e⟩ r hr hr2]
  show rkLin (m - 1 + 1) true q.card r (Nat.card (center K)) = _
  rw [hqc, Nat.sub_add_cancel (by omega)]

theorem uc22s2114_dvd_of_borelAut (hKA : KLieBorelAutPrime) {M L B : Subgroup G}
    (hL : L ∈ calC M) (hBL : B ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ B, CentralizesBar b L → b = 1) {t : StatedLieTag} {m f : ℕ}
    (hadm : StatedLieAdmissible t m 2 f) (hM : LieModel (BarInf L) t m 2 f)
    (hl : 3 ≤ PartTwo.S17.CS17LieRank t m) {b : G} (hb : b ∈ B) {r : ℕ} (hbr : orderOf b = r)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) {U : Subgroup (BarInf L)}
    (hU : IsSylowTwoOf U ⊤) (hUb : U.map (inducedBarInfAutHom L ⟨b, hBL hb⟩).toMonoidHom = U) :
    r ∣ 2 ^ (2 * f) - 1 ∧ (t ≠ .PSU → t ≠ .POmegaMinus → t ≠ .twistedE6 → r ∣ 2 ^ f - 1) := by
  refine hKA (BarInf L) t m f hadm hM hl U hU r hr hr5 hrf _ (fun h1 => ?_) ?_ hUb
  · have hb1 := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith hb h1
    rw [hb1, orderOf_one] at hbr
    omega
  · exact rhoInf_pow_eq_one L (hBL hb) (by rw [← hbr]; exact pow_orderOf_eq_one b)

theorem uc22s2114_four_le_pRank_of_lieRank_four (hT : LieOddRankChev)
    (hKC : PartTwo.Inputs1719.K_CartanRank) {M L : Subgroup G} (hL : L ∈ calC M)
    {t : StatedLieTag} {m f : ℕ} (hadm : StatedLieAdmissible t m 2 f)
    (hM : LieModel (BarInf L) t m 2 f) (hl : 4 ≤ PartTwo.S17.CS17LieRank t m) {r : ℕ}
    (hr : r.Prime) (hr7 : 7 ≤ r) (hrf : r ∣ 2 ^ f - 1) :
    4 ≤ CFSG.Open.pRank r L := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hM' := LieModel.of_mulEquiv e hM
  have hq := hL.2.2
  have hodd := uc22p20p_odd_center_bar2 ↥L
  have hr2 : r ≠ 2 := by omega
  rw [← pRank_bar2_eq_of_odd hr hr2]
  by_cases hpsl : t = .PSL
  · subst hpsl
    have hm : 5 ≤ m := by change 4 ≤ m - 1 at hl; omega
    rw [uc22s2114_pRank_psl_of_five_le hT hq (hM'.statedClassicalModel (by decide)) hm hr hr2]
    exact uc22p20v_four_le_rkLin_true_one hr (uc22p20v_eP_of_dvd hrf) hm (fun _ => by omega)
  · obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf (⊤ : Subgroup (Bar2 L))
    exact hl.trans ((hKC (Bar2 L) t m f hadm hM' hq hodd S hS r hr hr2 hrf
      (fun h => absurd h hpsl) (fun _ => by omega)).trans
      ((WeakClosure81.pRank_normalizerQuotient_le_normalizer S hS.2.1 hr hr2).trans
        (CFSG.SectionRank.pRank_mono hr.one_lt le_top)))


theorem uc22s2114_pRank_three_of_lieRank_four (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag} {m f : ℕ}
    (hadm : StatedLieAdmissible t m 2 f) (hM : LieModel (BarInf L) t m 2 f)
    (hl : 4 ≤ PartTwo.S17.CS17LieRank t m) :
    2 ≤ CFSG.Open.pRank 3 L ∧ (3 ≤ CFSG.Open.pRank 3 L ∨ (t = .PSL ∧ m = 5 ∧ Odd f)) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hM' := LieModel.of_mulEquiv e hM
  have hq := hL.2.2
  have hodd := uc22p20p_odd_center_bar2 ↥L
  have hf : 1 ≤ f := hadm.2.1
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
  suffices h : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ∨
      (t = .PSL ∧ m = 5 ∧ Odd f ∧ 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L))) by
    rcases h with h | h
    · exact ⟨by omega, Or.inl h⟩
    · exact ⟨h.2.2.2, Or.inr ⟨h.1, h.2.1, h.2.2.1⟩⟩
  cases t with
  | PSL =>
    have hm : 5 ≤ m := by change 4 ≤ m - 1 at hl; omega
    rw [uc22s2114_pRank_psl_of_five_le hT hq (hM'.statedClassicalModel (by decide)) hm
      Nat.prime_three (by norm_num)]
    by_cases hev : Even f
    · exact Or.inl (le_trans (by omega)
        (uc22p20v_rkLin_true_one (m := m) (by rw [uc22p20v_eP_three, if_pos hev])))
    · rw [uc22p20v_rkLin_true_two (by rw [uc22p20v_eP_three, if_neg hev] : eP (2 ^ f) 3 = 2)]
      by_cases hm5 : m = 5
      · exact Or.inr ⟨rfl, hm5, Nat.not_even_iff_odd.1 hev, by omega⟩
      · exact Or.inl (by omega)
  | PSU =>
    have hm : 8 ≤ m := by change 4 ≤ m / 2 at hl; omega
    rw [uc22p20w_pRank_psu hT hq (hM'.statedClassicalModel (by decide)) Nat.prime_three
      (by norm_num)]
    rcases uc22p20v_eM_three_cases f with h | h
    · exact Or.inl (le_trans (by omega) (uc22p20v_rkLin_false_one h))
    · exact Or.inl (by rw [uc22p20v_rkLin_false_two h]; omega)
  | PSp =>
    have hm : 4 ≤ m := hl
    rw [uc22p20w_pRank_psp hT hq (hM'.statedClassicalModel (by decide)) Nat.prime_three
      (by norm_num), uc22p20v_rkSp_of_eS (uc22p20v_eS_three f)]
    exact Or.inl (by omega)
  | POmegaOdd => exact (hadm.2.2.2 rfl).elim
  | POmegaPlus =>
    rw [uc22p20w_pRank_pomegaPlus hT hq (hM'.statedClassicalModel (by decide)) Nat.prime_three
      (by norm_num)]
    exact Or.inl (le_trans (by norm_num)
      (uc22p20v_rkOmPlus_ge hadm.2.2 (uc22p20v_eS_three f) (uc22p20v_eP_three_cases f)))
  | POmegaMinus =>
    have hm : 5 ≤ m := by change 4 ≤ m - 1 at hl; omega
    rw [uc22p20w_pRank_pomegaMinus hT hq (hM'.statedClassicalModel (by decide)) Nat.prime_three
      (by norm_num)]
    exact Or.inl (le_trans (by omega) (uc22p20v_rkOmMinus_ge (l := m) (uc22p20v_eS_three f)))
  | F4 =>
    exact Or.inl (le_trans (by norm_num) (uc22p20w_four_le_pRank_three_exc
      (uc22p20v_center_f4 hN hq hodd hM') (by simp) hf hM'))
  | E7 =>
    exact Or.inl (le_trans (by norm_num) (uc22p20w_four_le_pRank_three_exc
      (uc22p20v_center_e7 hN hq hodd hf hM') (by simp) hf hM'))
  | E8 =>
    exact Or.inl (le_trans (by norm_num) (uc22p20w_four_le_pRank_three_exc
      (uc22p20v_center_e8 hN hq hodd hM') (by simp) hf hM'))
  | E6 =>
    have hZd : Nat.card (center (Bar2 L)) ∣ Nat.gcd 3 (2 ^ f - 1) * 1 :=
      uc22p20v_card_center_dvd hN hq hodd hM'
    rw [mul_one] at hZd
    by_cases hZ : center (Bar2 L) = ⊥
    · exact Or.inl (le_trans (by norm_num) (uc22p20w_four_le_pRank_three_exc hZ (by simp) hf hM'))
    · have h3 : 3 ∣ Nat.card (center (Bar2 L)) := by
        rcases (Nat.dvd_prime Nat.prime_three).1 (hZd.trans (Nat.gcd_dvd_left 3 _)) with h | h
        · exact absurd (Subgroup.card_eq_one.mp h) hZ
        · exact dvd_of_eq h.symm
      exact Or.inl (le_trans (by norm_num)
        ((CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankLowerUntw (Bar2 L) m 2 f hM'
          ((h3.trans hZd).trans (Nat.gcd_dvd_right 3 _))).1 h3))
  | twistedE6 =>
    have hZd : Nat.card (center (Bar2 L)) ∣ Nat.gcd 3 (2 ^ f + 1) * 1 :=
      uc22p20v_card_center_dvd hN hq hodd hM'
    rw [mul_one] at hZd
    by_cases hZ : center (Bar2 L) = ⊥
    · exact Or.inl (le_trans (by norm_num) (uc22p20w_four_le_pRank_three_exc hZ (by simp) hf hM'))
    · have h3 : 3 ∣ Nat.card (center (Bar2 L)) := by
        rcases (Nat.dvd_prime Nat.prime_three).1 (hZd.trans (Nat.gcd_dvd_left 3 _)) with h | h
        · exact absurd (Subgroup.card_eq_one.mp h) hZ
        · exact dvd_of_eq h.symm
      exact Or.inl (le_trans (by norm_num)
        ((CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankLowerTw (Bar2 L) m 2 f hM'
          ((h3.trans hZd).trans (Nat.gcd_dvd_right 3 _))).1 h3))
  | _ => simp [PartTwo.S17.CS17LieRank] at hl

theorem s21_14R4_setup4_of_residuals (hGA : GriessAllModelsStatement)
    (hN : uc22p20rNativeGriess) (hKA : KLieBorelAutPrime) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hPart : PartIAt S.M) (Ch : Choice2011 G)
    (hn3 : H1930 (UC6.dataOfSetup4 hS hU S) → ∀ c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch, 3 ≤ c.n)
    (h3 : S21_3 (UC6.dataOfSetup4 hS hU S) Ch) (h5 : S21_5 (UC6.dataOfSetup4 hS hU S) Ch)
    (hF : S21_14R4F (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_14R4 (UC6.dataOfSetup4 hS hU S) Ch := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := uc22p20x_lieOddRankChev hGA
  have hKC := PartTwo.Inputs1719.k_CartanRank_of_griess_of_twistedE6 hN
    (PartTwo.Inputs1719.k_CartanRank_twistedE6_of_griess hN)
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  rintro hH c L hL hX hpow ⟨l, f, hl4, t, m, hadm, hmod, rfl⟩
  have hn3' := hn3 hH c
  have hBL := uc22s2114_B0_le_normalizer h5 hH c hL
  obtain ⟨h23, h33⟩ := uc22s2114_pRank_three_of_lieRank_four hT hN hL hadm hmod hl4
  have hfaith := uc22s2114_faithful h3 hH c hL (fun hthin => by
    have := hthin 3 Nat.prime_three (by norm_num)
    omega)
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hTL := uc22p2214_isSylowOf_inf (UC6.dataOfSetup4 hS hU S).sylowM hL.1
  have hbor : ∀ r : ℕ, r.Prime → 7 ≤ r → r ∣ 2 ^ c.n - 1 → ¬ r ∣ f → (Odd c.n ∨ t = .PSL) →
      ∀ b (hb : b ∈ c.B0), orderOf b = r → ∀ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ →
        U.map (inducedBarInfAutHom L ⟨b, hBL hb⟩).toMonoidHom = U → False := by
    intro r hr hr7 hrn hrf hcase b hb hbr U hUs hUb
    obtain ⟨hr2f, hrf'⟩ := uc22s2114_dvd_of_borelAut hKA hL hBL hfaith hadm hmod (by omega) hb
      hbr hr (by omega) hrf hUs hUb
    have h1 : r ∣ 2 ^ f - 1 := by
      rcases hcase with hodd | rfl
      ·
        have hg : Nat.gcd c.n (2 * f) ∣ f := Nat.Coprime.dvd_of_dvd_mul_left
          (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) (Nat.coprime_two_right.2 hodd))
          (Nat.gcd_dvd_right _ _)
        exact (uc22s2114_dvd_two_pow_gcd_sub_one (d := 2 * f) (f := 1) hodd
          ⟨0, (pow_zero 2).symm⟩ hrn (by rwa [mul_one])).trans
            (Nat.pow_sub_one_dvd_pow_sub_one 2 hg)
      · exact hrf' (by decide) (by decide) (by decide)
    exact uc22s2114_not_mem_sig hSg hns hH c hr hrn (hSg.four_mem r hr (by omega)
      ((uc22s2114_four_le_pRank_of_lieRank_four hT hKC hL hadm hmod hl4 hr hr7 h1).trans
        (CFSG.SectionRank.pRank_mono hr.one_lt hL.1.le)))
  by_cases hodd : Odd c.n
  ·
    refine hF hH c L hL hX hpow _ f hl4 ⟨t, m, hadm, hmod, rfl⟩ hn3' hBL hfaith (Or.inl hodd) ?_
    intro r hr hr5 hrn
    by_contra hrf
    have hr7 := P2251h.seven_le_of_dvd_two_pow_sub_one (by omega)
      (uc22p20v_not_three_dvd_sub_one hodd) hr hrn
    obtain ⟨b, hb, hbr⟩ := uc22p22i_exists_elt_of_mem_piSet
      (show r ∈ piSet c.B0 by rw [c.hpi]; exact ⟨hr, hrn⟩)
    obtain ⟨U, hUs, hUb⟩ := uc22s2114_exists_map_eq hTL (hBL hb) (c.B0_le_normalizer hodd hb)
    exact hbor r hr hr7 hrn hrf (Or.inl hodd) b hb hbr U hUs hUb
  have h3n : 3 ∣ 2 ^ c.n - 1 := (by norm_num : 3 ∣ 2 ^ 2 - 1).trans
    (Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)))
  by_cases hL5 : t = .PSL ∧ m = 5 ∧ Odd f
  · obtain ⟨rfl, rfl, hfo⟩ := hL5
    by_cases hf1 : f = 1
    · subst hf1
      by_cases h4 : 4 ∣ c.n
      · exact (uc22s2114_false_of_isL5_two c hL hmod h4 hBL hfaith).elim
      obtain ⟨n', hn'⟩ := Nat.not_odd_iff_even.1 hodd
      have hn'odd : Odd n' := by
        rcases Nat.even_or_odd n' with ⟨k, hk⟩ | h
        · exact absurd ⟨k, by omega⟩ h4
        · exact h
      obtain ⟨r, hr, hrn'⟩ := uc22p20v_exists_prime_dvd_sub_one (n := n') (by
        obtain ⟨k, hk⟩ := hn'odd
        omega)
      have hr7 := P2251h.seven_le_of_dvd_two_pow_sub_one (by obtain ⟨k, hk⟩ := hn'odd; omega)
        (uc22p20v_not_three_dvd_sub_one hn'odd) hr hrn'
      have hrn : r ∣ 2 ^ c.n - 1 := hrn'.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨2, by omega⟩)
      obtain ⟨b, hb, hbr⟩ := uc22p22i_exists_elt_of_mem_piSet
        (show r ∈ piSet c.B0 by rw [c.hpi]; exact ⟨hr, hrn⟩)
      have hmem : b ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ n' - 1} c.B0 := by
        refine uc22pwtb_mem_oPi c.hB0.2.1 hb fun p hp hpb => ?_
        rw [hbr] at hpb
        rw [(Nat.prime_dvd_prime_iff_eq hp hr).1 hpb]
        exact ⟨hr, hrn'⟩
      have hbT := c.hα 1 n' hn'odd (by rw [pow_one]; omega) hmem
      obtain ⟨U, hUs, hUb⟩ := uc22s2114_exists_map_eq hTL (hBL hb) hbT
      obtain ⟨h21, -⟩ := uc22s2114_dvd_of_borelAut hKA hL hBL hfaith hadm hmod (by omega) hb hbr
        hr (by omega) hr.not_dvd_one hUs hUb
      have h3r : r ∣ 3 := by simpa using h21
      have := Nat.le_of_dvd (by norm_num) h3r
      omega
    have hf3 : 3 ≤ f := by
      obtain ⟨k, hk⟩ := hfo
      omega
    refine hF hH c L hL hX hpow _ f hl4 ⟨.PSL, 5, hadm, hmod, rfl⟩ hn3' hBL hfaith
      (Or.inr ⟨hmod, hfo, hf3⟩) ?_
    intro r hr hr5 hrn
    by_contra hrf
    obtain ⟨b, hb, hbr⟩ := uc22p22i_exists_elt_of_mem_piSet
      (show r ∈ piSet c.B0 by rw [c.hpi]; exact ⟨hr, hrn⟩)
    obtain ⟨U, hUs, hUb⟩ := uc22s2114_exists_map_eq_of_solvOver c hL
      (fun U hU => S15.K21dTitsProof.solvOver_of_lieModel (by omega) (Or.inl rfl) hmod hU) hb
      (hBL hb)
    by_cases hr5' : r = 5
    · subst hr5'
      obtain ⟨-, h5f⟩ := uc22s2114_dvd_of_borelAut hKA hL hBL hfaith hadm hmod (by omega) hb hbr
        hr hr5 hrf hUs hUb
      obtain ⟨k, hk⟩ := CFSG.Assembly.e6Four_five_dvd_two_pow_sub_one.1
        (h5f (by decide) (by decide) (by decide))
      obtain ⟨j, hj⟩ := hfo
      omega
    have hr7 : 7 ≤ r := by
      rcases (show r = 5 ∨ r = 6 ∨ 7 ≤ r by omega) with h | h | h
      · exact absurd h hr5'
      · exact absurd (h ▸ hr) (by norm_num)
      · exact h
    exact hbor r hr hr7 hrn hrf (Or.inr rfl) b hb hbr U hUs hUb
  exact (uc22s217u3a_false_of_sp _ Ch hH c Nat.prime_three h3n
    (PartOne.Section8.isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL
      (h33.resolve_right hL5))).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
