module

public import CFSG.LocalAnalysis.StandardType.GGKSmall7D6
public import CFSG.LocalAnalysis.StandardType.GGKSmall7E6
public import CFSG.LocalAnalysis.StandardType.GGKSmall7Read
public import CFSG.LocalAnalysis.StandardType.GGDepED4LE3Close
public import CFSG.LocalAnalysis.StandardType.GGDepED4LE3Up7
public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwoNodeLE3K7_weyl
    (hUse : ZS.UseInput) (hAll : LR6E6All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hLoc : GGE6D4TwoNodeLocalInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrowK : GGResRowAt ggRowTwoNodeSmallJD p J K)
    (hL3 : GGResLeviSideDatumLE3 p Bs L J) (h7 : Nat.card ↥Bs = 3 ^ 7) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall, htagD⟩ := hrowK
  have hrow2 : ggRowTwoNode p labJ labX := hrowSmall.1
  obtain ⟨hrank, hp3, hXtag⟩ := ggQ2s08_ce6_rowD4 hrow2 htagD
  subst hp3
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hx1 : x ≠ 1 := ggTK_x_ne_one hH
  obtain ⟨-, -, -, hXK, hJ192, hKd⟩ := hLoc G B Bs x L D J y K hH K y
    (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hrow2 hXtag
  have hLd := ggResTwoNodeSideDatum_of_LE3_seven hx hLx hx1 h7 hJ192 hL3
  have hA := ggDepED4_align_two_weyl (by norm_num) hXK.core hKd hLd hJ192
  rcases ggKSmall7_cases_of_alignedW hA with hXL | hD
  · exact ggKSmall7_e6_weyl hAll hOrb hFix hFixK hH h7 hXL hXK.core hLd hKd hJ192
  · exact ggKSmall7_d6_weyl hUse hOrb hFix hFixK hH h7 hD

end CFSG.StandardType

end
