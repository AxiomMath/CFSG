module

public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CAssembly

public section

namespace CFSG.StandardType

theorem GGSecFiveRestHyp.resXDatum_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J) :
    GGResXDatum p Bs L := by
  have hc : GGConfig p B Bs x L D J := hR.1
  obtain ⟨y, K, hN⟩ := exists_ggNbr hc.1.2.2.2.2.2.2.2 hc.2.2
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hc, hR.2.1, hR.2.2.1, hR.2.2.2.1, hN, hW y K hN, Or.inr hW⟩
  refine (hX G p B Bs x L D J y K hH).1.resolve_right ?_
  rintro ⟨labJ, labX, hΛJ, hΛX, hlabJ, hlabX, hp7, h5⟩
  exact ggSeven_L_absurd hTCJ hRig hc hp7 hN hΛX hlabX h5

theorem GGSecFiveRestHyp.weylReflectionGroup_L {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs) := by
  have : Fact p.Prime := ⟨(GGConfig.tableB_facts hR.1).1⟩
  exact HdRo7C.weyl_of_xDatum (hR.resXDatum_L hX hTCJ hRig hW)

theorem GGSecFiveRestHyp.resXDatum_nbr {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hn : GGNbr p B x D J y K) : GGResXDatum p Bs K := by
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hn, hW y K hn, Or.inr hW⟩
  refine (hX G p B Bs x L D J y K hH).2.resolve_right ?_
  rintro ⟨-, labX, -, hΛX, -, hlabX, hp7, h5⟩
  exact ggSeven_K_absurd hTCJ hRig hTPn hA8 hraw hiso hH hp7 hΛX hlabX h5

theorem GGSecFiveRestHyp.weylReflectionGroup_nbr {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hn : GGNbr p B x D J y K) : GGWeylReflectionGroup p (ggAutomizer K Bs) := by
  have : Fact p.Prime := ⟨(GGConfig.tableB_facts hR.1).1⟩
  exact HdRo7C.weyl_of_xDatum (hR.resXDatum_nbr hX hTCJ hRig hTPn hA8 hraw hiso hW hn)

end CFSG.StandardType

end
