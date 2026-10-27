module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterSpor
public import CFSG.Quasithin.Background.A318POutHe
public import CFSG.Quasithin.Background.A318POutMore
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.RankThree.PartTwo.Sec4.Item47Native

import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3


theorem exists_eq_conj_of_isSpor {L : Type} [Group L] [Finite L] {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨ s = .He ∨
      s = .Ru ∨ s = .J4)
    (h : UC22.IsSpor L s) (φ : MulAut L) (hφ : ∃ n : ℕ, φ ^ (3 ^ n) = 1) :
    ∃ k : L, φ = MulAut.conj k := by
  obtain ⟨e⟩ := h
  have hOut : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) := by
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact CFSG.Quasithin.A318P.not_dvd_outer_M11 e Nat.prime_three (by norm_num)
    · exact
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.not_three_dvd_card_outer_of_isSpor_m12
          ⟨e⟩
    · exact CFSG.Quasithin.A318P.not_dvd_outer_M22 e Nat.prime_three (by norm_num)
    · exact CFSG.Quasithin.A318P.not_dvd_outer_M23 e Nat.prime_three (by norm_num)
    · exact CFSG.Quasithin.A318P.not_dvd_outer_M24 e Nat.prime_three (by norm_num)
    · exact CFSG.Quasithin.A318P.not_dvd_outer_of_carrier e
        CFSG.RankThree.PartTwo.Sec4.card_outer_J2 Nat.prime_three (by norm_num)
    · exact CFSG.Quasithin.A318P.not_dvd_outer_HS e Nat.prime_three (by norm_num)
    · exact CFSG.Quasithin.A318P.not_dvd_outer_He e Nat.prime_three (by norm_num)
    · exact CFSG.Quasithin.A318P.not_dvd_outer_Ru e Nat.prime_three (by norm_num)
    · exact
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.not_three_dvd_card_outer_of_isSpor_J4
          ⟨e⟩
  obtain ⟨n, hn⟩ := hφ
  obtain ⟨k, hk⟩ := CFSG.AGLEmbedding.mem_inner_of_pow_prime_pow_eq_one
    Nat.prime_three hOut hn
  exact ⟨k, hk.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
