module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588D1
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C622
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Main

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.RepresentationTheory
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

open N588

theorem c622_direct (m : Mz614 Dat) (_h69 : R6_9 Dat) (h619 : m.C619)
    (hL : m.L620) : m.C622 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hX : m.r = 3 ∧ IsAlt m.Lbar 6 ∨ K318.List620' m.r m.Lbar := by
    rcases hL.2 with h | h | h
    · by_cases hr3 : m.r = 3
      · exact Or.inl ⟨hr3, isAlt_six_of_psl_two h hr3⟩
      · exact Or.inr (Or.inl ⟨hr3, h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases hX with ⟨hr3, hA⟩ | hX
  · exact Or.inr ⟨hr3, hA⟩
  have hs : IsSimpleGroup m.Lbar := (K318.simple_card_of_list620 hX).1
  have hnc := m.Lbar_not_comm hL.1 hs
  obtain ⟨-, hperf, hdich⟩ := quasisimple_or_centralizer_le (r := m.r)
    (P := CFSG.pPrimeCore m.r ↥m.L) m.isSolvable_pPrimeCore_L CFSG.pPrimeCore_coprime_card hs hnc
    m.gen_L
  rcases hdich with hq | hcent
  · exact Or.inl hq
  exfalso
  haveI : Group.IsPerfect ↥m.L := ⟨hperf⟩
  obtain ⟨q, hq, hqY, d, hd, φ, hφ⟩ := K318.exists_linear_section (CFSG.pPrimeCore m.r ↥m.L)
    m.isSolvable_pPrimeCore_L m.odd_card_pPrimeCore_L
    (fun p hp hp2 => m.pRank_pPrimeCore_L_le_three h619 hp hp2) hcent hs
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 m.odd_card_pPrimeCore_L) (even_iff_two_dvd.2 hqY)
  have hqr : q ≠ m.r := by
    rintro rfl
    have hcop := CFSG.pPrimeCore_coprime_card (p := m.r) (G := ↥m.L)
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hqY)
  exact K318.false_of_linear_section m.hr m.d.odd hq hq2 hqr hX (CFSG.pPrimeCore m.r ↥m.L)
    m.isSolvable_pPrimeCore_L m.odd_card_pPrimeCore_L (MulEquiv.refl _) hd φ hφ

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
