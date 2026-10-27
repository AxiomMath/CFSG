module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Ap3
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Ap4
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Exp32
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Rank2
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Pxq

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem sec34_APData (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x)
    (hKp : KProper InCatalog G) (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D)
    (hU : FF79Sec34UFacts b a J A) (hoa : orderOf a = 3)
    (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) (haC : a ∈ CenS (U34 b a J A)) :
    FF79APData (cqβ (U34 b a J A) b hU.b_nor) (cqImg (U34 b a J A) (U34 b a J A))
      (cqImg (U34 b a J A) (Lay (J ⊓ Cen a)))
      (QuotientGroup.mk (⟨a, haC⟩ : ↥(CenS (U34 b a J A)))) := by
  obtain ⟨b3, core, absyl, Zc, Zcard, z0m, z0o, z0f, A4⟩ := sec34_ap_basic hs h hU hoa hK haC
  obtain ⟨Ka5, Kfix, Knor, Kcc⟩ := sec34_ap_K hs h hU hoa hK
  exact ⟨b3, core, absyl, Zc, Zcard, z0m, z0o, z0f, A4, Ka5, Kfix,
    ap_pxq _ b3 _ Ka5 Kfix Kcc, Knor, sec34_ap_no27 hs h hU, sec34_ap_rank2 hs h hU,
    sec34_ap_exp3 hs h hU, sec34_ap_catalog hG hna hKp hs h hU⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
