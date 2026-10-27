module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.ActionV
public import CFSG.RankThree.GF2n.Parrott.Setup

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem pi_conjJ'_mul_inv (h : Tim79a.ParrottHyp z) (b : H z) (j : J z) :
    QuotientV.pi z (conjJ' z b j * j⁻¹) =
      conjV h b (QuotientV.pi z j) * (QuotientV.pi z j)⁻¹ := by
  rw [map_mul, map_inv, conjV_mk]

end CFSG.RankThree.GF2n.Parrott
