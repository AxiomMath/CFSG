module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LE3Close
public import CFSG.LocalAnalysis.StandardType.GGDepED4Up7
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Seven

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2s08_ce6_alignedW_of_LE3_seven {G : Type} [Group G] [Finite G] {Bs L J K : Subgroup G}
    {y : G} (hy : y ∈ Bs) (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) (hy1 : y ≠ 1)
    (hCard : Nat.card ↥Bs = 3 ^ 7) (hXL : GGResXDatumE6Core 3 Bs L)
    (hLd : GGResTwoNodeSideDatum 3 Bs L J) (hJ192 : Nat.card ↥(ggAutomizer J Bs) = 192)
    (hK3 : GGResLeviSideDatumLE3 3 Bs K J) : GGDepED4AlignedW 3 2 Bs L J K :=
  ggDepED4_align_two_weyl (by norm_num) hXL hLd
    (ggResTwoNodeSideDatum_of_LE3_seven hy hKy hy1 hCard hJ192 hK3) hJ192

theorem ggDepED4_false_LE3_L7 (hLoc : GGE6D4TwoNodeLocalInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrowL : GGResRowAt ggRowTwoNodeSmallJD p J L)
    (hxL : x ∉ L) (hK3 : GGResLeviSideDatumLE3 p Bs K J) (h7 : Nat.card ↥Bs = 3 ^ 7) : False := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall, htagD⟩ := hrowL
  have hrow2 : ggRowTwoNode p labJ labX := hrowSmall.1
  obtain ⟨hrank, hp3, hXtag⟩ := ggQ2s08_ce6_rowD4 hrow2 htagD
  subst hp3
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  obtain ⟨-, -, -, hXL, hJ192, hLd⟩ := hLoc G B Bs x L D J y K hH L x
    (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hrow2 hXtag
  exact ggDepED4Up7_false hFix hFixK hH hxL rfl h7
    (ggQ2s08_ce6_alignedW_of_LE3_seven hy hKy hy1 h7 hXL.core hLd hJ192 hK3)

end CFSG.StandardType

end
