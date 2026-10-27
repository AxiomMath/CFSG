module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedBadLine
public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedFinal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourJoin
public import CFSG.LocalAnalysis.StandardType.GGNewPlaneLocalAction
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppPlusSup
import CFSG.LocalAnalysis.StandardType.GGF4N2OriginalJoin
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

@[expose] def GGF4N2MixedGenInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (Rd Ra : Prop), GGSecFiveRestGen 5 B Bs x L D J Rd Ra →
    ∀ (y : G) (K : Subgroup G), GGNbr 5 B x D J y K →
      GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      GGCentralImage .POmegaMinus 4 2 L → GGCentralImage .PSL 6 2 K →
        GGCentralImage .E6 0 2 (ggG0 5 B x L D J)


theorem ggF4N2OmegaK_altPlane_mixed {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hdata : GGF4N2AltPlaneData B Bs x L K) :
    ∃ (D' J' : Subgroup G) (d : G) (A : Subgroup G),
      GGSecFiveRestGen 5 B Bs x L D' J' True True ∧ GGNbr 5 B x D' J' d A ∧
        GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer A Bs) ∧
        GGCentralImage .PSL 6 2 A ∧ ggG0 5 B x L D' J' = L ⊔ K := by
  obtain ⟨-, -, -, -, -, -, -, -, D', J', d, A, -, -, -, -, hcfg', hnbr, -, -, -, -, -, -, -,
    hAimg, -, hLA, -, hLKA, hlocal⟩ := hdata
  have hRg : GGSecFiveRestGen 5 B Bs x L D' J' True True :=
    GGSecFiveRestGen.of_local hcfg' hR.2.1 ⟨hR.2.2.1.1, fun z Y hz => (hlocal z Y hz).1⟩
      hR.2.2.2.1
  have hF4A : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer A Bs) := by
    rw [hLA]
    exact hF4
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG0, -⟩ :=
    ggF4N2_mixed_E6_reduction hLB hRg hnbr hL hAimg hF4A
  exact ⟨D', J', d, A, hRg, hnbr, hF4A, hAimg, hG0.trans hLKA.symm⟩

theorem ggF4N2OmegaK_centralImage_sup_of_mixed (hMix : GGF4N2MixedGenInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hdata : GGF4N2AltPlaneData B Bs x L K) :
    GGCentralImage .E6 0 2 (L ⊔ K) := by
  obtain ⟨D', J', d, A, hRg, hnbr, hF4A, hAimg, hG0⟩ :=
    ggF4N2OmegaK_altPlane_mixed hR hF4 hL hdata
  rw [← hG0]
  exact hMix G B Bs x L D' J' True True hRg d A hnbr hF4A hL hAimg

theorem ggF4N2MixedGenInput_holds : GGF4N2MixedGenInput := by
  intro G _ _ B Bs x L D J Rd Ra hR y K hNbr hF4 hL hK
  exact ggF4N2_mixed_centralImage hR hNbr hL hK hF4

theorem ggF4N2OmegaK_centralImage_sup {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hdata : GGF4N2AltPlaneData B Bs x L K) :
    GGCentralImage .E6 0 2 (L ⊔ K) :=
  ggF4N2OmegaK_centralImage_sup_of_mixed ggF4N2MixedGenInput_holds hR hF4 hL hdata

theorem ggF4N2OmegaK_centralImage_of_routeCfg
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {K : Subgroup G} (hRC : GGSecFiveRouteCfg 5 B Bs x L D J {K})
    (hWF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hdata : GGF4N2AltPlaneData B Bs x L K) :
    GGCentralImage .E6 0 2 (ggG0 5 B x L D J) := by
  rw [ggG0_eq_sup_of_routeCfg_F4 hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM hRC hWF4]
  exact ggF4N2OmegaK_centralImage_sup hRC.1 hWF4 hL hdata

theorem ggF4N2AltPlaneData_of_inputs (hLB : GGLBalanceInput)
    (hNPLA : GGNewPlaneLocalActionInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 5 B Bs x L D J) (hW : GGSecFiveWeylCase' 5 B Bs x D J)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo 5 Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr 5 B x D J y K)
    (hWF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .POmegaMinus 4 2 K) :
    GGF4N2AltPlaneData B Bs x L K := by
  obtain ⟨e', w, n, hpres, hnLK, hnN, hn, hnc, D', J', d, A, hD', hJ', hD'x, hStd,
    hcfg', hnbr, hAdef, hAn, hJA, hhJ, hZJ, hInnA, hhA, hAimg, hEnd, hLA, hle⟩ :=
    ggF4N2OmegaK_altPlane hLB hNPLA hR hW hq hNb hWF4 hL
  have hLKA : L ⊔ K = L ⊔ A :=
    ggF4N2Omega_sup_eq_of_automizer_inclusion hR hNb hWF4 hL hK hle (hLA ▸ hWF4)
      (le_sup_right.trans hLA.le)
  exact ⟨e', w, n, hpres, hnLK, hnN, hn, hnc, D', J', d, A, hD', hJ', hD'x, hStd, hcfg',
    hnbr, hAdef, hAn, hJA, hhJ, hZJ, hInnA, hhA, hAimg, hEnd, hLA, hle, hLKA,
    fun z Y hz => ⟨hNPLA G 5 B Bs x L D J hR D' J' hStd z Y hz,
      ggNbr_halfSplit_of_hyp hraw hiso hcfg' hz (hNPLA G 5 B Bs x L D J hR D' J' hStd z Y hz)⟩⟩

theorem ggF4N2_centralImage_of_routeCfg
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M) (hLB : GGLBalanceInput)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hRC : GGSecFiveRouteCfg 5 B Bs x L D J {K})
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo 5 Bs L) (hNb : GGNbr 5 B x D J y K)
    (hWF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K ∨ GGCentralImage .POmegaMinus 4 2 K) :
    GGCentralImage .E6 0 2 (ggG0 5 B x L D J) := by
  rcases hK with hMix | hOm
  · exact ggF4N2_mixed_centralImage hRC.1 hNb hL hMix hWF4
  · exact ggF4N2OmegaK_centralImage_of_routeCfg hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM hRC
      hWF4 hL (ggF4N2AltPlaneData_of_inputs hLB hNPLA hraw hiso hRC.1 hRC.2.1 hq hNb hWF4 hL hOm)

end CFSG.StandardType

end
