module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourTwins
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGF4Absorption
import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal

theorem ggG0_eq_sup_of_routeCfg_F4
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {K : Subgroup G} (hR : GGSecFiveRouteCfg p B Bs x L D J {K})
    (hWK : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    ggG0 p B x L D J = L ⊔ K := by
  obtain ⟨e, he⟩ := hWK
  have hJ : ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ggAutomizerJoin_singleton L Bs K
  let e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizerJoin L Bs {K}) :=
    e.trans (MulEquiv.subgroupCongr hJ.symm)
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hP : GGCoxeterPres p (ggAutomizerJoin L Bs {K}) CoxeterMatrix.F₄ e' :=
    ⟨hF4W, fun i => he i⟩
  have hF4 : GGIsWeylMatrixF4 CoxeterMatrix.F₄ :=
    ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩
  have hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) →
      (b : G) ∈ Subgroup.zpowers x := fun b hb =>
    ((GGSecFiveRestHyp.fixLineComp_L hTBF hR.1 hR.2.1).fix_iff b).1 hb
  have hWL : GGWeylReflectionGroup p (ggAutomizer L Bs) :=
    GGSecFiveRestHyp.weylReflectionGroup_L hX hTCJ hRig hR.1 hR.2.1
  have hRM' : ∀ y K', GGNbr p B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs {K} := fun y K' hn =>
    hRM G p B Bs x L D J {K} hR (Fin 4) CoxeterMatrix.F₄ e' hP hF4 y K' hn
  have hWK' : ∀ y K', GGNbr p B x D J y K' →
      GGWeylReflectionGroup p (ggAutomizer K' Bs) := fun y K' hn =>
    GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR.1 hR.2.1 hn
  have hF1 : ∀ y K', GGNbr p B x D J y K' → ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer K' Bs, a b = b) → (b : G) ∈ Subgroup.centralizer (K' : Set G) :=
    fun y K' hn b hb =>
      hFC G p B Bs x L D J y K'
        ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hn, hR.2.1 y K' hn, Or.inr hR.2.1⟩ b hb
  rw [ggSecFiveF4Join_of_suppliers hR hP hF4 hFixL hWL hRM' hWK' hF1, Finset.iSup_singleton]

theorem ggF4QGeFourJoinInput_of_suppliers
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M) (row : GGF4QGeFourRow) :
    GGF4QGeFourJoinInput row := by
  intro G _ _ p B Bs x L D J y K _ hR e hpres f _ _ _
  exact ggG0_eq_sup_of_routeCfg_F4 hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM hR ⟨e, hpres.2⟩

end CFSG.StandardType

end
