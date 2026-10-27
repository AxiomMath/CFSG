module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenTorus
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem s21_normalSp4_of (D : Data G) (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D)
    (h211 : S21_1 D Ch) : S21_NormalSp4 D Ch := by
  intro hH c L hL n hn hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := hL.1.le
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLM]
  by_contra hML
  have hn3 : 3 ≤ n := uc22p218d_three_le_of_odd hX hn
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrn
  have hZ : ¬ r ∣ Nat.card (center (Bar2 L)) := by
    rw [uc22p218d_center_eq_bot_sp4 hX, Subgroup.card_bot]
    exact hr.not_dvd_one
  obtain ⟨E, hEL, hEel, hEc⟩ := CFSG.SectionRank.exists_pRank hr.one_lt L
  rw [uc22p218c_pRank_eq_two_of_bar2 hX hr hrn] at hEc
  have h4 : 4 ≤ CFSG.Open.pRank r D.M := by
    have := UC6S846.calCRankTwice D.M L hL hML r hr hr2 hZ E hEL hEel 2 hEc
    omega
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) (hSg.four_mem r hr hr2 h4)
  have hT₁ : IsPGroup 2 (D.T ⊓ normalizer (L : Set G) : Subgroup G) :=
    D.sylowM.isPGroup.to_le inf_le_left
  have hTL : IsSylowOf 2 ((D.T ⊓ normalizer (L : Set G) : Subgroup G) ⊓ L) L := by
    rw [inf_assoc, inf_eq_right.2 (le_normalizer : L ≤ normalizer (L : Set G))]
    exact uc22p2214_isSylowOf_inf D.sylowM hL.1
  obtain ⟨y, hyL, hy, hyN⟩ :=
    uc22p218c_exists_orderOf_eq_mem_normalizer_sp4 hT₁ inf_le_right hTL hX hn dvd_rfl hrn
  obtain ⟨x, hxcl, hx, hxN⟩ := exists_mem_conjClosure_orderOf_mem_normalizer D.sylowM hL hr hr2
    hZ ⟨y, hyL, hy, zpowers_le.1 hyN⟩
  have hclM : conjClosure D.M L ≤ D.M := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, hg, rfl⟩ := hK
    rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using D.M.mul_mem (D.M.mul_mem hg (hLM hz)) (D.M.inv_mem hg)
  have hxp : IsPGroup r (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hx1 : zpowers x ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot.1 h, orderOf_one] at hx
    exact hr.one_lt.ne hx
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hr hr2 hx
    (uc22p22r_mem_uniqueSet_of_sp D hr hsp ((zpowers_le.2 hxcl).trans hclM) hxp hx1)
    (zpowers_le.2 hxN)

end CFSG.LocalAnalysis.UniquenessCase.UC22
