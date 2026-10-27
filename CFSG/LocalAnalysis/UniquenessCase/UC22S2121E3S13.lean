module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xe
public import CFSG.LocalAnalysis.UniquenessCase.UC22S219Sig3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen5
import CFSG.LocalAnalysis.UniquenessCase.UC22S13g
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xn
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3Pow
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3R847
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_setting13_r847E3
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h847T : R847E3Thin D)
    (h211 : S21_1 D Ch) (h216 : S21_16 D Ch) (h218 : S21_18 D Ch) (h219 : S21_9Sig3 D Ch)
    (h19 : S21_19 D Ch) (he : evenRank G = 3) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (hH : Hyp2120 D c) : PartTwo.Setting13 D :=
  have hsig := uc22s13xe_sig_eq_sig1 hSig h61 c hH
  ⟨hsig, uc22s13xe_hyp131_of_isPowTwo hThin hCyc hSig h61
    (uc22s2121e3_r847Four_of_r847E3Thin h847T h61 c hH) h211 h216 h218
    (uc22s2121e3_isPowTwo_of_s21_9Sig3 he h1930 c hH h219) h19 h1930 c hH hsig⟩

theorem uc22s2121e3_pRank_eq_three {D : Data G} (hSig : UC6S846.SigmaStd D)
    (he : evenRank G = 3) {p : ℕ} (hp : p ∈ D.sig) : CFSG.Open.pRank p D.M = 3 := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hpp hp2 D.M
    D.maxLocal.1
  have h3 := hSig.three_le p hp
  omega

theorem uc22s2121e3_pRank_eq_sum (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hS : PartTwo.Setting13 D) (hSig : UC6S846.SigmaStd D) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p D.M = ∑ J ∈ PartTwo.s13_compsP (Bar2 D.M) p, CFSG.Open.pRank p J +
      CFSG.Open.pRank p (F13.Sp D.M p) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have h := PartTwo.s13_pRank_bar_eq_add hThin hCyc D hS hSig hp
  rwa [PartTwo.s13_pRank_bar_top hpp hp2, PartTwo.s13_pRank_pElementSubgroup_layer
    (PartTwo.s13_normalSimple hThin D hS) hpp hpp, ← PartTwo.s13_barImage_Sp D.M hpp,
    PartTwo.s13_pRank_barImage hpp hp2 (PartTwo.s13_Sp_le D.M p)] at h

theorem uc22s2121e3_pRank_le_of_mem_calC {D : Data G} (hH : F13.Hyp131 D) {p : ℕ}
    (hpp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.Open.pRank p L ≤ 1 ∨
      ((∃ n, IsPowTwo n ∧ IsU3 (Bar2 L) n ∧ p ∣ 2 ^ n + 1) ∧ CFSG.Open.pRank p L ≤ 2) := by
  obtain hthin | ⟨n, hn, hU⟩ := hH.thinOrU3 L hL
  · exact Or.inl (hthin p hpp hp2)
  by_cases hpn : p ∣ 2 ^ n + 1
  · have h2 := CFSG.Quasithin.B69K.pRank_le_two_of_psu3
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hU) hpp hp2
    rw [pRank_bar2_eq_of_odd hpp hp2] at h2
    exact Or.inr ⟨⟨n, hn, hU, hpn⟩, h2⟩
  · exact Or.inl (uc22s13xn_pRank_le_one hL hU hpp hp2 hpn)

theorem uc22s2121e3_shape
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hS : PartTwo.Setting13 D) (hSig : UC6S846.SigmaStd D) (hrk3 : PartTwo.SigmaRankThree13 D)
    (h846 : F08.R846 D) (h847 : R847Four D) {L : Subgroup G} (hL : L ∈ calC D.M) :
    ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) := by
  obtain ⟨n, hn, h⟩ | ⟨n, hn, h⟩ := PartTwo.isL2_or_isU3_of_mem_calC D hS hSig hThin hCyc hrk3
    (r133_of hThin hCyc D h846 h847 hSig.nonempty) hL
  exacts [⟨n, hn, Or.inl h⟩, ⟨n, hn, Or.inr h⟩]

end CFSG.LocalAnalysis.UniquenessCase.UC22
