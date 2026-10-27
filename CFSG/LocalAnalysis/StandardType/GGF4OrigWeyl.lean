module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResF4
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CAssembly
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrXInnerWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4Orig_xDatum_of_route
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    @GGResXDatum G _ _ p ⟨(GGConfig.tableB_facts hcfg.1.1).1⟩ Bs L := by
  have hp : p.Prime := (GGConfig.tableB_facts hcfg.1.1).1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrest : GGSecFiveRestHyp p B Bs x L D J := hcfg.1
  have hW : GGSecFiveWeylCase' p B Bs x D J := hcfg.2.1
  have hc : GGConfig p B Bs x L D J := hrest.1
  obtain ⟨y, K, hN⟩ := exists_ggNbr hc.1.2.2.2.2.2.2.2 hc.2.2
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hc, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hN, hW y K hN, Or.inr hW⟩
  rcases (hX G p B Bs x L D J y K hH).1 with hD | hRow
  · exact hD
  · obtain ⟨labJ, labX, hΛJ, hΛX, hlabJ, hlabX, hp7, h5⟩ := hRow
    have h5' : GGSevenLabel labX := h5
    exact (ggSeven_L_absurd hTCJ hRig hc hp7 hN hΛX hlabX h5').elim

theorem ggF4Orig_weyl_of_route
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    GGWeylReflectionGroup p (ggAutomizer L Bs) := by
  haveI : Fact p.Prime := ⟨(GGConfig.tableB_facts hcfg.1.1).1⟩
  exact HdRo7C.weyl_of_xDatum (ggF4Orig_xDatum_of_route hX hTCJ hRig hcfg)

end CFSG.StandardType

end
