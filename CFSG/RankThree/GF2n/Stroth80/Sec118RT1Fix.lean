module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

variable [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem Ctx.two_mul_le_of_card_commXbarPre (hc : Ctx M Q Z B) {n m : ℕ} (hw : Width Q Z n)
    (hcard : Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ (4 * m + 1)) : 2 * m ≤ n := by
  have hle : (Z ⊔ ⁅Q, XbarPre M Q Z B⁆ : Subgroup G) ≤ Q :=
    sup_le hc.Z_le_Q (commutator_le_Q hc)
  have h1 : Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) ≤ Nat.card Q := Subgroup.card_le_of_le hle
  rw [hcard, hw] at h1
  have hZ2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have := (Nat.pow_le_pow_iff_right hZ2).mp h1
  omega

end CFSG.RankThree.GF2n.Stroth80
