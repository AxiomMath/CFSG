module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Torus
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric
public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Parity
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4FrameAux
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley

theorem ggF4Row_labelAll_adjoint
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : GGTableBF4Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift p 4 R ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
        (_ : R ≃* ↥(adjointGroup Tag.F4 K)), p ∣ Nat.card K - 1 ∧
          I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, TableBF4.ggTorusLift_F4 hp hp2 hpq, K,
    inferInstance, inferInstance, this, TableBF4.recipeEquiv K, hpq,
    TableBF4.idImage_subset_inn K⟩

theorem ggTBJTorusNoncomm_rowR4
    (hRig : GGLabelRigidInput) :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR4 p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN y hy hy1 J' hJ' hJl hcount
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hLF : GGInnerDiagOnLabel GGTableBF4Label p Bs L :=
    ggInnerDiagOnLabel_f4Split_of_rowR4 hRig hHyp hL
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGTableBF4Label p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggF4Row_labelAll_adjoint hp hp2 hs))
    (fun _ _ _ _ _ _ hP => hP.1) hLF
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, hlift, K, _, _, _, e, hpq, hIinn⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      ↥(adjointGroup Tag.F4 K) →* MulAut ↥(adjointGroup Tag.F4 K))) e (fun φ hφ => by
    obtain ⟨g, rfl⟩ := hIinn hφ
    exact ⟨e g, by
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  exact ggTBJ_f4_torusJNoncomm hp hp2 hpq (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB' y hy hJ'
    hJl hcount

theorem ggTBJNaWeylQFourOn_rowR4
    (hRig : GGLabelRigidInput) :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR4 p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm (ggTBJTorusNoncomm_rowR4 hRig)

end CFSG.StandardType

end
