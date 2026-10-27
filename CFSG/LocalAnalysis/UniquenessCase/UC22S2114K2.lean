module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Borel
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC6L34C626
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_center_bar2_eq_bot_of_isU (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) (hX : IsU4 (BarInf L) 1 ∨ IsU5 (BarInf L) 1) : center (Bar2 L) = ⊥ := by
  have hodd : Odd (Nat.card (center (Bar2 L))) := uc22p20p_odd_center_bar2 ↥L
  have h2 : Nat.card (center (Bar2 L)) ∣ 2 := by
    rcases hX with hX | hX
    · have hg : genericOrders .PSU 4 2 1 = (1, 1) := rfl
      have he : exceptionalOrders .PSU 4 2 1 = (2, 1) := rfl
      have h := card_center_bar2_dvd_of_row hL (t := .PSU) (n := 4) (p := 2) (f := 1)
        (by rw [hg, he]; norm_num) (griessRow_of_lieModel_classical hGA hX (by decide))
      rw [hg, he] at h
      simpa using h
    · exact (card_center_bar2_dvd_of_isU5 hGA hL hX).trans (by norm_num)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact Subgroup.card_eq_one.1 h
  · rw [h] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.2 even_two)

theorem uc22s2114_le_pRank_three_of_psu {X : Type} [Group X] [Finite X] {m : ℕ}
    (hX : LieModel X .PSU (m + 1) 2 1) (hm : ¬ 3 ∣ m + 1) :
    m ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (LieModel.statedClassicalModel hX (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU (LieModel.admissible hX)
      (MulEquiv.refl (CFSG.PGLModel.projSU (m + 1) 2 1)))
  have : Finite (CFSG.PGLModel.projSU (m + 1) 2 1) := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, hE, hcard⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.exists_elemAbelian_projSU_torus m 2 1 le_rfl
      (by norm_num) hm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

theorem uc22s2114_three_le_pRank_of_isU (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) (hX : IsU4 (BarInf L) 1 ∨ IsU5 (BarInf L) 1) :
    3 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2
    (uc22s2114_center_bar2_eq_bot_of_isU hGA hL hX)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
  rcases hX with hX | hX
  · exact uc22s2114_le_pRank_three_of_psu (m := 3) (LieModel.of_mulEquiv e hX) (by norm_num)
  · exact le_trans (by norm_num)
      (uc22s2114_le_pRank_three_of_psu (m := 4) (LieModel.of_mulEquiv e hX) (by norm_num))

theorem uc22s2114_k_eq_one_of_isU (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hPart : PartIAt S.M) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hX : IsU4 (BarInf L) 1 ∨ IsU5 (BarInf L) 1) :
    (UC6.dataOfSetup4 hS hU S).k = 1 := by
  show CFSG.LocalAnalysis.RankThreeUC.kParam S.M = 1
  rw [CFSG.LocalAnalysis.RankThreeUC.kParam,
    if_pos (PartOne.Section8.isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL
      (uc22s2114_three_le_pRank_of_isU hGA hL hX))]

theorem uc22s2114_isPowTwo_n_of_isL3 {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : IsL3 (BarInf L) f) (hf : IsPowTwo f)
    (hBL : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    (hn3 : 3 ≤ c.n) : IsPowTwo c.n ∧ 4 ∣ c.n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : IsSylowOf 2 (D.T ⊓ L) L := uc22p2214_isSylowOf_inf D.sylowM hL.1
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (n := c.n) (by omega)
  have hm1 : m = 1 := by
    by_contra hm1
    have hm3 : 3 ≤ m := by
      obtain ⟨j, rfl⟩ := hm
      omega
    have h1 : 2 ^ m - 1 ≠ 1 := by
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      omega
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd h1
    have h3m : ¬ 3 ∣ 2 ^ m - 1 := fun h =>
      uc22s2114_not_dvd_of_odd (f := 2) hm ⟨1, by norm_num⟩ Nat.prime_three h (by norm_num)
    have hr7 := P2251h.seven_le_of_dvd_two_pow_sub_one (by omega) h3m hr hrm
    have hrn : r ∣ 2 ^ c.n - 1 :=
      hrm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨2 ^ e, by rw [hnm, mul_comm]⟩)
    have hrB : r ∣ Nat.card c.B0 := by
      have h : r ∈ piSet c.B0 := by
        rw [c.hpi]
        exact ⟨hr, hrn⟩
      exact h.2
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
    have hbr : (b : G) ^ r = 1 := by
      rw [← Subgroup.orderOf_coe] at hb
      rw [← hb]
      exact pow_orderOf_eq_one _
    have hbT : (b : G) ∈ normalizer (D.T : Set G) := c.hα e m hm hnm
      (uc22pwtb_mem_oPi c.hB0.2.1 b.2 fun p hp hpb => by
        rw [Subgroup.orderOf_coe, hb] at hpb
        rw [(Nat.prime_dvd_prime_iff_eq hp hr).1 hpb]
        exact ⟨hr, hrm⟩)
    have hb1 : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ≠ 1 := fun h1 => by
      have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
      exact hr.ne_one hb.symm
    exact uc22s2114_not_dvd_of_odd hm hf hr hrm
      (uc22s2114_dvd_of_borel_l3 hL hTL hX hf (hBL b.2) hbT hr hr7 hbr hb1)
  subst hm1
  rw [mul_one] at hnm
  refine ⟨⟨e, hnm⟩, ?_⟩
  have he : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with he | he
    · interval_cases e <;> simp at hnm <;> omega
    · exact he
  rw [hnm]
  exact (by norm_num : 4 ∣ 2 ^ 2).trans (Nat.pow_dvd_pow 2 he)

theorem uc22s2114_n_eq_four_of_isL3_two {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hX : IsL3 (BarInf L) 2)
    (hBL : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    (hn : IsPowTwo c.n) (h4 : 4 ∣ c.n) : c.n = 4 := by
  obtain ⟨k, hk⟩ := hn
  by_contra hne
  have h4' : 2 ^ 2 ∣ 2 ^ k := by
    rw [← hk]
    exact h4
  have hk3 : 3 ≤ k := lt_of_le_of_ne ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h4')
    fun h => hne (by subst h; simpa using hk)
  have h8 : 8 ∣ c.n := by
    rw [hk]
    exact (by norm_num : 8 ∣ 2 ^ 3).trans (Nat.pow_dvd_pow 2 hk3)
  have h17 : 17 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 17 ∣ 2 ^ 8 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 h8)
  have h17B : 17 ∣ Nat.card c.B0 := by
    have h : 17 ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨by norm_num, h17⟩
    exact h.2
  have h := h17B.trans (uc22s2114_card_dvd_aut hL hBL hfaith)
  rw [UC6.L34K.lieModel_card_mulAut hX] at h
  norm_num at h

end CFSG.LocalAnalysis.UniquenessCase.UC22
