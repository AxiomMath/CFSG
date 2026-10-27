module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LFFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)
open CFSG.Open

variable {G : Type} [Group G] [Finite G]


theorem s21_14R3LF_dataOfSetup (hGA : GriessAllModelsStatement) (hS : Standing G)
    (hUC : CFSG.Open.rankThreeUC G) (S : Setup G)
    (h74 : F07.R74Card (PartTwo.Three.dataOfSetup hS S)) :
    S21_14R3LF (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
  rintro hH c L hL _ _ f hX _ hk hodd hn3 hBT hBL hfaith
  exfalso
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (n := 2 ^ c.n - 1) (by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn3
    omega)
  have : Fact r.Prime := ⟨hr⟩
  have h3n : ¬ 3 ∣ 2 ^ c.n - 1 := fun h =>
    uc22s2114_not_dvd_of_odd (f := 2) hodd ⟨1, by norm_num⟩ Nat.prime_three h (by norm_num)
  have hr7 := P2251h.seven_le_of_dvd_two_pow_sub_one (by omega) h3n hr hrn
  have hrB : r ∣ Nat.card c.B0 := by
    have h : r ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hr, hrn⟩
    exact h.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
  have hbr : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hb]
  have hb1 : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ≠ 1 := fun h1 => by
    have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
    exact hr.ne_one hb.symm
  by_cases hin : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range
  · obtain ⟨-, h3L, hrσ, -, -⟩ := r3lf_inner_context hGA (UC6S846.sigmaStd_dataOfSetup hS S) hH c
      hL hX (hBL b.2) (hBT b.2) hr hr7 hbr hrn hodd hb1 hin
    exact hrσ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hr hr7
      (h3L.trans (CFSG.SectionRank.pRank_mono hr.one_lt hL.1.le)))
  · exact r3lf_false_of_outer hGA h74 (uc22p2251h_isStronglyPEmbedded _ hk) hH c hL hX b.2
      (hBL b.2) hr hr7 hbr hin

end CFSG.LocalAnalysis.UniquenessCase.UC22
