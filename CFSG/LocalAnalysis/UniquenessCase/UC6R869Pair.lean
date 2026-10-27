module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThreeStrong
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC6R77E2
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 Theorem614At)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

namespace R869S

theorem two_le_pRank_pair_of_isL2 {M K : Subgroup G} (hK : K ∈ calC M)
    (hc2 : (conjSetOf M K).ncard = 2) {n : ℕ} (hL2 : IsL2 (Bar2 K) n) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsK : s ∣ Nat.card (Bar2 K)) : 2 ≤ CFSG.Open.pRank s (conjClosure M K) := by
  haveI := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  refine P2214R.two_le_pRank_pair hK hc2 hs hs2 ?_
  rw [uc22p21k_center_eq_bot hK.2.2, Subgroup.index_bot]
  exact hsK

end R869S

theorem r869NPair_dataOfSetup4 (hSS : StronglyEmbeddedSolvable)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (h614 : Theorem614At S.M) :
    F08.R869NPair (dataOfSetup4 hS hU S) := by
  intro K hK hc2 n hn2 hnpow hL2 r hr hr2 A hAM hAr hcov
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK
  have hLperf := R869S.perfect_of_isProdOfCalC hprod
  obtain ⟨m, rfl⟩ : 4 ∣ n := by
    obtain ⟨j, rfl⟩ := hnpow
    rcases j with _ | _ | j
    · norm_num at hn2
    · norm_num at hn2
    · exact ⟨2 ^ j, by ring⟩
  have h3n : 3 ∣ 2 ^ (4 * m) - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (x := 2 ^ 4) (y := 1) (n := m)
    rw [one_pow, ← pow_mul] at h
    exact (by norm_num : 3 ∣ 2 ^ 4 - 1).trans h
  have hdvd : ∀ s : ℕ, s ∣ 2 ^ (4 * m) - 1 ∨ s ∣ 2 ^ (4 * m) + 1 →
      s ∣ Nat.card (Bar2 K) := by
    intro s hs
    rw [uc22p22r_L2_card hL2]
    refine Dvd.dvd.mul_left ?_ _
    have hfac : (2 ^ (4 * m)) ^ 2 - 1 = (2 ^ (4 * m) + 1) * (2 ^ (4 * m) - 1) := by
      have := Nat.sq_sub_sq (2 ^ (4 * m)) 1
      simpa using this
    rw [hfac]
    rcases hs with hs | hs
    · exact hs.mul_left _
    · exact hs.mul_right _
  by_cases h3M : IsStronglyPEmbedded 3 (dataOfSetup4 hS hU S).M
  ·
    exact R869S.normalizer_le_of_strongThree hS hK3 h3M hXM hLperf
      (R869S.two_le_pRank_pair_of_isL2 hK hc2 hL2 Nat.prime_three (by norm_num)
        (hdvd 3 (Or.inl h3n))) hr hAM hAr hcov
  ·
    have h3 : 3 ∉ uniqueFourBeta G := fun h =>
      h3M (UC22.isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h)
    rcases uc22ine229_cong_of_ncard_two (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
        (r77E2_dataOfSetup4 hSE hS hU S h3) ((r6_14_dataOfSetup4_iff hS hU S).2 h614) hK hc2
        (Or.inl hL2) Nat.prime_three (by norm_num) h3n h3M S.hp with ⟨-, hcong⟩ | ⟨hSz, -⟩
    · have hpp : S.p.Prime := S.hp.1.1
      have hp2 : S.p ≠ 2 := S.hp.1.2.1
      have hpd : S.p ∣ 2 ^ (4 * m) + 1 := by
        have h1 := hcong.symm.dvd
        rw [sub_neg_eq_add] at h1
        exact_mod_cast h1
      have hp5 : S.p ≠ 5 := by
        rintro h5
        rw [h5] at hpd
        have h16 : 2 ^ (4 * m) % 5 = 1 := by
          rw [pow_mul, Nat.pow_mod]
          norm_num
        generalize 2 ^ (4 * m) = x at hpd h16
        omega
      exact r869NS5_dataOfSetup4 hSS hSE hS hU S h3 _ hXM hMX hprod
        ⟨S.p, S.hp, R869S.two_le_pRank_pair_of_isL2 hK hc2 hL2 hpp hp2 (hdvd _ (Or.inr hpd)),
          fun h => absurd h hp5⟩ r hr hr2 A hAM hAr hcov
    ·
      exact absurd (hdvd 3 (Or.inl h3n))
        (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)

end CFSG.LocalAnalysis.UniquenessCase.UC6
