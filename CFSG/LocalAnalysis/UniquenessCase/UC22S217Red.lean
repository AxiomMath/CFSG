module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213f
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_17_of_residual (D : Data G) (Ch : Choice2011 G) (he : 3 < CFSG.Open.evenRank G)
    (h16 : S21_16 D Ch) (h15T : S21_15Two D Ch) (hSp : S21_NormalSp4 D Ch) (hR : S21_17R D Ch)
    (h8100E : R8100E D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) : S21_17 D Ch := by
  intro h1930 c L hL
  have hLM : L ≤ D.M := hL.1.le
  by_cases hN : (L.subgroupOf D.M).Normal
  · exact Or.inl (uc22p2214_conjClosure_eq_of_normal hLM hN).symm
  have hne : conjClosure D.M L ≠ L := fun h =>
    hN (uc22p21j_normal_of_conjClosure_eq hLM h.symm)
  obtain ⟨hSU, hpow2, hA5, hq, hJ⟩ := hR h1930 c L hL hN
  have hc2 : (conjSetOf D.M L).ncard ≤ 2 → (conjSetOf D.M L).ncard = 2 := fun hle => by
    have hpos : 0 < (conjSetOf D.M L).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨L, ⟨1, D.M.one_mem, by ext x; simp⟩⟩
    have h1 : (conjSetOf D.M L).ncard ≠ 1 := fun h1 =>
      hne (uc22s217_conjClosure_eq_of_ncard_eq_one h1)
    omega
  have hpow2' : IsPowTwo 2 := ⟨1, (pow_one 2).symm⟩
  have hL4 : ¬ IsL2 (Bar2 L) 2 := fun hL2 => by
    have h2 := hc2 (hpow2 2 hpow2' hL2)
    exact uc22p2213f_false_of_powTwo D Ch h8100E h1930 he c (hn3 h1930 c) (hA5 h2 hL2) hL h2
      le_rfl hpow2' hL2
  rcases h16 h1930 c L hL with ⟨n, hn, hSp4⟩ | ⟨n, hU⟩ | ⟨n, hL2⟩ | ⟨n, hSz⟩ |
      ⟨p, hp, hp2, hLp⟩ | hJ1
  · exact absurd (hSp h1930 c L hL n hn hSp4) hN
  · exact absurd hU (hSU n)
  · have hn2 : 2 ≤ n := PartTwo.s13_two_le_of_isL2 hL2
    have hn : 2 < n := by
      rcases (show n = 2 ∨ 2 < n by omega) with rfl | hn
      · exact absurd hL2 hL4
      · exact hn
    by_cases hpow : IsPowTwo n
    · exact Or.inr (Or.inl ⟨hc2 (hpow2 n hpow hL2), n, hn, Or.inl hL2⟩)
    · exact Or.inr (Or.inl ⟨h15T h1930 c L hL n (Or.inr ⟨hL2, hpow⟩) hne, n, hn, Or.inl hL2⟩)
  · have hn : 3 ≤ n := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
    exact Or.inr (Or.inl ⟨h15T h1930 c L hL n (Or.inl hSz) hne, n, by omega, Or.inr hSz⟩)
  · by_cases h5 : 5 < p
    · exact absurd hLp (hq p hp h5)
    have h3 : p ≠ 3 := by
      rintro rfl
      exact CFSG.Open.StatedAPI.not_psl_two_of_statedLieAdmissible_three_one hLp.admissible
        ⟨rfl, rfl⟩
    have hp5 : p = 5 := by
      have h2le := hp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · exact absurd rfl h3
      · exact absurd hp (by norm_num)
      · rfl
    subst hp5
    exact absurd (PartTwo.s13_isL2_two_of_isL2Odd_five hLp) hL4
  · have := hJ hJ1
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
