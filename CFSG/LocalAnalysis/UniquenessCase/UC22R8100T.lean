module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213TDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem r8100T_of_r77E2 (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) : R8100T D := by
  intro _ K hK hc2 n hn hpow hL2 h3 p hp
  obtain ⟨j, rfl⟩ := hpow
  have hj : j ≠ 0 := by
    rintro rfl
    norm_num at hn
  have h3n : 3 ∣ 2 ^ 2 ^ j - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_pow_self 2 hj)
  rcases uc22ine229_cong_of_ncard_two hSg h77 h614 hK hc2 (Or.inl hL2) Nat.prime_three
      (by norm_num) h3n h3 hp with ⟨-, h⟩ | ⟨hSz, -⟩
  · exact h
  · exact absurd (CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz)
      (Nat.not_odd_iff_even.2 ((Nat.even_pow' hj).2 even_two))

end CFSG.LocalAnalysis.UniquenessCase.UC22
