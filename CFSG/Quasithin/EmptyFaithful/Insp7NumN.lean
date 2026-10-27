module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumM
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Insp7

theorem numFactAt_u33 : NumFactAt (fun L _ => StatedClassicalModel L .PSU 3 3 1) := by
  refine numFactAt_of_not_dvd_aut (fun L _ _ _ hL hdvd => ?_)
  obtain ⟨h1, -, h3, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound L 3 3 1 hL
  have hcard : Nat.card L = 6048 := by
    have h2 : (Nat.card L : ℤ) = 6048 := by
      have h := h1
      norm_num [Finset.prod_Icc_succ_top] at h
      omega
    exact_mod_cast h2
  have hout : Nat.card (Outer L) = 2 := by
    rw [h3]
    norm_num
  have h4 := hdvd.trans (card_mulAut_dvd_mul_outer L)
  rw [hcard, hout] at h4
  exact absurd h4 (by decide)

theorem numFactAt_u34 : NumFactAt (fun L _ => StatedClassicalModel L .PSU 3 2 2) := by
  refine numFactAt_of_not_nine_dvd_aut (fun L _ _ _ hL hdvd => ?_)
  obtain ⟨h1, -, h3, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound L 3 2 2 hL
  have hcard : Nat.card L = 62400 := by
    have h2 : (Nat.card L : ℤ) = 62400 := by
      have h := h1
      norm_num [Finset.prod_Icc_succ_top] at h
      omega
    exact_mod_cast h2
  have hout : Nat.card (Outer L) = 4 := by
    rw [h3]
    norm_num
  have h4 := hdvd.trans (card_mulAut_dvd_mul_outer L)
  rw [hcard, hout] at h4
  exact absurd h4 (by decide)

end Insp7

end CFSG.Quasithin
