module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB1AAAAAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {U : Type} [CommGroup U] [Finite U]

theorem s16h_L3_sum_three_seven_fixed_mem_fixV {L : Subgroup (MulAut U)}
    (helem : ∀ u : U, u * u = 1)
    (hquasi : CFSG.Open.IsQuasisimple ↥L) (hsl3 : IsSLn ↥L 3 1)
    (hcomm : commSub ⊤ L = ⊤)
    (hsum : ∃ k : ℕ, k ≤ 3 ∧
      SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ (fixV L) k)
    {g : MulAut U}
    (hgc : g ∈ Subgroup.centralizer (L : Set (MulAut U)))
    (hg7 : g ^ 7 = 1)
    (hgZ : ∀ z : U, z ∈ fixV L → g z = z)
    (hn : ¬ ∀ u : U, g u * u⁻¹ ∈ fixV L) :
    ∀ u : U, g u = u → u ∈ fixV L := by
  rcases s16h_L3_sum_three_seven_dichotomy helem hquasi hsl3 hcomm hsum hgc hg7 hgZ with
    htriv | hfix
  · exact (hn htriv).elim
  · exact hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
