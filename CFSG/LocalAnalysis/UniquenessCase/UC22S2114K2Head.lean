module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2N
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Sp4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2G2D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Five
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114D4
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]


theorem s21_14K2_setup4 (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hPart : PartIAt S.M) (Ch : Choice2011 G)
    (h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S)) :
    S21_14K2 (UC6.dataOfSetup4 hS hU S) Ch := by
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have h614 : UC6.R6_14 (UC6.dataOfSetup4 hS hU S) :=
    (UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1
  have h4 : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
      4 ≤ CFSG.Open.pRank p (UC6.dataOfSetup4 hS hU S).M :=
    fun p hp => UC6.four_le_pRank_of_sigma hp
  intro hH c L hL _ hpow hcase _ hn3 hBL hfaith
  exfalso
  have key : ∀ f : ℕ, LieRankTwoEven (BarInf L) f → 4 ∣ c.n ∧ IsPowTwo f := by
    intro f hRT
    have hf := hpow f hRT
    rcases uc22s2114_four_dvd_n_of_lieRankTwo c hL hRT hf hBL hfaith hn3 with h | ⟨hD, h36⟩
    · exact ⟨h, hf⟩
    · exact (uc22s2114_false_of_is3D4_of_three_dvd hSg h614 h76 h4 hH c hL hD hf
        (by omega)).elim
  have h2 : ∀ k : ℕ, 2 ≤ 2 ^ k → 2 ∣ 2 ^ k := fun k hk =>
    dvd_pow_self 2 (by rintro rfl; norm_num at hk)
  rcases hcase with ⟨f, hf2, hSp | hG2 | hU4 | hU5⟩ | ⟨f, hD⟩
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inl hSp))
    exact uc22s2114_false_of_isSp4 hGA hSg h614 h76 h4 hH c hL hSp (h2 k hf2)
      ((dvd_mul_right 2 2).trans hn)
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inl hG2)))
    rcases k with _ | _ | k
    · norm_num at hf2
    · exact uc22s2114_false_of_isG2_four c hL (by simpa using hG2) hn hBL hfaith
    · exact uc22s2114_false_of_isG2 hSg h614 h76 h4 hH c hL hG2 ⟨2 ^ k, by ring⟩ hn
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hU4))))))
    exact uc22s2114_false_of_isU4_even hGA hSg h614 h76 h4 hH c hL hU4 (h2 k hf2)
      ((dvd_mul_right 2 2).trans hn)
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hU5))))))
    exact uc22s2114_false_of_isU5 hGA hSg h614 h76 h4 hH c hL hU5 (h2 k hf2) hn
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inr (Or.inl hD))))
    rcases k with _ | _ | k
    · exact uc22s2114_false_of_is3D4_two c hL (by simpa using hD) hn hBL hfaith
    · exact uc22s2114_false_of_is3D4_four c hL (by simpa using hD) hn hBL hfaith
    · exact uc22s2114_false_of_is3D4_four_dvd hSg h614 h76 h4 hH c hL hD ⟨2 ^ k, by ring⟩ hn

end CFSG.LocalAnalysis.UniquenessCase.UC22
