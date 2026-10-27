module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U7KFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3URank
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UBorel
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3Tor
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PC
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySixB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanSylowAbelianHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]


theorem uc22s2114r3u_false_of_torus (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {m f : ℕ}
    (hm : m = 6 ∨ m = 7) (hX : LieModel (BarInf L) .PSU m 2 f) {r : ℕ} (hr : r.Prime)
    (hr7 : 7 ≤ r) (hrn : r ∣ 2 ^ c.n - 1) (hrf : ¬ r ∣ f) (hrq : r ∣ 2 ^ f - 1)
    (hU7T : PartTwo.Inputs1719.K_U7CentTorus)
    (hU7S : PartTwo.Inputs1719.K_U7CartanSylowAbelian) : False := by
  have hr2 : r ≠ 2 := by omega
  have hadm := LieModel.admissible hX
  have h1 : 2 ^ f + 1 ≠ 1 := by
    have : 0 < 2 ^ f := by positivity
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by have := hadm.2.1; omega)
    omega
  have hpσ : p ∈ D.sig := hSg.four_mem p hp hp2
    ((uc22s2114r3u_four_le_pRank hGA hL (by omega) hX hp hp2 (fun h => absurd h (by omega))
      hpd).trans (CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le))
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hXq : LieModel (Bar2 L ⧸ center (Bar2 L)) .PSU m 2 f := LieModel.of_mulEquiv e hX
  have hqK : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hoddK := uc22p20p_odd_center_bar2 ↥L
  obtain ⟨E, hEel, hEc, hEp⟩ : ∃ E : Subgroup (Bar2 L), IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (centralizer (E : Set (Bar2 L)))) := by
    rcases hm with rfl | rfl
    · exact PartTwo.Inputs1719.k_RankThreeCentTorus_u6 (Bar2 L) f p r hadm hXq hqK hoddK hp hp2
        hpd hr (by omega) hrq
    · exact hU7T (Bar2 L) f p r hadm hXq hqK hoddK hp hp2 hpd hr hr7 hrq
  have hab : ∀ P : Sylow r (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)) := by
    rcases hm with rfl | rfl
    · exact PartTwo.Inputs1719.k_CartanSylowAbelian_holds (Bar2 L) .PSU 6 f r hadm hXq hqK hoddK
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hr (by omega) hrq
    · exact hU7S (Bar2 L) f r hadm hXq hqK hoddK hr hr7 hrq
  have hout : ¬ r ∣ Nat.card (Outer (Bar2 L)) := by
    rcases hm with rfl | rfl
    · exact PartTwo.not_dvd_card_outer_bar2 hL hX (Or.inr (Or.inl ⟨rfl, rfl⟩)) hr (by omega) hrf
    · exact uc22s2114r3u_not_dvd_card_outer_u7 hL hX hr (by omega) hrf
  obtain ⟨E', _, -, -, rfl, hEtel, hEtc, hle⟩ :=
    PartTwo.S17.exists_lift_elemAbelian_pRank_centralizer hr hr2 hp hp2 hL.1.le hEel hEc
  exact uc22s2114r3_false_of_centralizer hSg h614 h76 hH c hL hr hr2 hrn
    (uc22s2114r3u_not_dvd_card_center hGA hL hm hX hr hr7) hab hout hpσ
    (Subgroup.map_subtype_le E') hEtel hEtc (hEp.trans hle)

theorem s21_14R3U_setup4_of_residuals (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hPart : PartIAt S.M) (Ch : Choice2011 G)
    (h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S))
    (hn3 : H1930 (UC6.dataOfSetup4 hS hU S) → ∀ c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch, 3 ≤ c.n)
    (h3 : S21_3 (UC6.dataOfSetup4 hS hU S) Ch) (h5 : S21_5 (UC6.dataOfSetup4 hS hU S) Ch)
    (hF : S21_14R3UF (UC6.dataOfSetup4 hS hU S) Ch)
    (hU7T : PartTwo.Inputs1719.K_U7CentTorus)
    (hU7S : PartTwo.Inputs1719.K_U7CartanSylowAbelian) :
    S21_14R3U (UC6.dataOfSetup4 hS hU S) Ch := by
  rintro hH c L hL hX hpow ⟨f, hf⟩
  obtain ⟨m, hm, hXm⟩ : ∃ m, (m = 6 ∨ m = 7) ∧ LieModel (BarInf L) .PSU m 2 f :=
    hf.elim (fun h => ⟨6, Or.inl rfl, h⟩) fun h => ⟨7, Or.inr rfl, h⟩
  have h3L := uc22s2114r3u_three_le_pRank_three hGA hL hm hXm
  have hSE := PartOne.Section8.isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL h3L
  have hk : (UC6.dataOfSetup4 hS hU S).k = 1 := by
    show CFSG.LocalAnalysis.RankThreeUC.kParam S.M = 1
    rw [CFSG.LocalAnalysis.RankThreeUC.kParam, if_pos hSE]
  have hodd : Odd c.n := u4p_odd_n _ Ch hH c hSE
  have hBT := u4x_B0_le_normalizer c hodd
  have hthin : ¬ F08.Thin8 L := fun h => by
    have := h 3 Nat.prime_three (by norm_num)
    omega
  have hBL := uc22s2114_B0_le_normalizer h5 hH c hL
  have hfaith := uc22s2114_faithful h3 hH c hL hthin
  by_cases hall : ∀ r : ℕ, r.Prime → r ∣ 2 ^ c.n - 1 → r ∣ f
  · exact hF hH c L hL hX hpow f hf hall hk hodd (hn3 hH c) hBT hBL hfaith
  push Not at hall
  obtain ⟨r, hr, hrn, hrf⟩ := hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have h3n : ¬ 3 ∣ 2 ^ c.n - 1 := fun h =>
    uc22s2114_not_dvd_of_odd (f := 2) hodd ⟨1, by norm_num⟩ Nat.prime_three h (by norm_num)
  have hr7 := P2251h.seven_le_of_dvd_two_pow_sub_one (by have := hn3 hH c; omega) h3n hr hrn
  have hrB : r ∣ Nat.card c.B0 := by
    have h : r ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hr, hrn⟩
    exact h.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
  have hbr : (b : G) ^ r = 1 := by
    rw [← Subgroup.orderOf_coe] at hb
    rw [← hb]
    exact pow_orderOf_eq_one _
  have hb1 : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ≠ 1 := fun h1 => by
    have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
    exact hr.ne_one hb.symm
  have h2f := uc22s2114r3u_dvd_of_borel hL
    (uc22p2214_isSylowOf_inf (UC6.dataOfSetup4 hS hU S).sylowM hL.1) hm hXm (hBL b.2)
    (hBT b.2) hr hr7 hrf hbr hb1
  have hrq : r ∣ 2 ^ f - 1 :=
    (uc22s2114_dvd_two_pow_gcd_sub_one (d := f) (f := 2) hodd ⟨1, rfl⟩ hrn
      (by rwa [mul_comm])).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_right c.n f))
  exact (uc22s2114r3u_false_of_torus hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1) h76 hH c hL hm hXm hr hr7 hrn hrf hrq
    hU7T hU7S).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
