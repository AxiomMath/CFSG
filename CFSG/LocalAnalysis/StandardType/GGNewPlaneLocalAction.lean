module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGNewPlaneLocalActionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ∀ D' J' : Subgroup G, LargeEvenStdSub p B x L D' J' →
      ∀ (z : G) (A : Subgroup G), GGNbr p B x D' J' z A → GGInnerDiagOn Bs A

theorem GGSecFiveRestHyp.config_of_stdSub {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp p B Bs x L D J)
    {D' J' : Subgroup G} (hStd : LargeEvenStdSub p B x L D' J') : GGConfig p B Bs x L D' J' :=
  ⟨hR.1.1, hR.1.2.1, hStd⟩

theorem ggNewPlaneLocalActionInput_of (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGNewPlaneLocalActionInput := by
  intro G _ _ p B Bs x L D J hR D' J' hStd z A hn
  have hC' : GGConfig p B Bs x L D' J' := hR.config_of_stdSub hStd
  have hNT : GGNoTransvection p Bs := hR.2.2.2.1
  have hN := hnorm G p B Bs x L D' J' hC' z A hn
  have h5 := (hC'.1.2.2.2.2.2.2.2.2.2.1 z A (isNeighborOf_of_ggNbr hC'.2.2 hn)).2
  have hM := hfield G p B Bs x L D' J' hC' z A hn hN _
    (hgraph G p B Bs x L D' J' hC' z A hn hN _ h5)
  refine largeEvenMarking_mono ?_ hM
  rintro lab R _ I F θ ⟨⟨-, hall⟩, himp⟩
  refine ⟨hN, fun b hb => ⟨_, ?_, largeEvenInduces_ggLAut_inv A θ (hN (Bs.inv_mem hb))⟩⟩
  by_contra hnot
  obtain ⟨φ, hφ, htv⟩ := himp hall ⟨b⁻¹, Bs.inv_mem hb, hnot⟩
  exact hNT φ hφ htv

end CFSG.StandardType

end
