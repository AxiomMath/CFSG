module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.PartThree.Twelve.FiveChart
import CFSG.OddTranspositions.PartThree.Twelve.NineFive
import CFSG.OddTranspositions.PartThree.Twelve.SixFiveLocal
import CFSG.OddTranspositions.PartThree.Twelve.SixFiveThree
import CFSG.OddTranspositions.PartThree.Twelve.SixFiveFive

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem twelveSix_five (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k)
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty)
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveChart hC (k + 1)) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d) :
    ∃ z, IsFiveHyperplane c w z := by
  have hn : 5 ≤ k + 1 := by omega
  have hΓ := hdiam w hw hwd
  rcases c.orderOf_mul_pivot hw hwd hΓ with h3 | h5
  · exact c.isFiveHyperplane_three hn hw hwd h3 hΓ
  · exact FiveChart.isFiveHyperplane_five hα hcen c hn hw hwd h5 hΓ

end CFSG.OddTranspositions.PartThree
