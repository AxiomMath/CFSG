module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric
public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpParity
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpFrameAux
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggSpRow_recipe_adjoint {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 1 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r : ℕ, 1 ≤ r ∧ GGTorusLift p r R ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (_ : CharP K 2) (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K r)), p ∣ Nat.card K - 1 ∧
          I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have hch : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have : NeZero l := ⟨by omega⟩
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, hl,
    TableBSymp.ggTorusLift_symplectic hp hp2 hpq hl, K, inferInstance, inferInstance, hch,
    MulEquiv.refl _, hpq, TableBSymp.sp_I_subset_inn⟩

theorem ggSpRow_labelAll_adjoint {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r : ℕ, 1 ≤ r ∧ GGTorusLift p r R ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (_ : CharP K 2) (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K r)), p ∣ Nat.card K - 1 ∧
          I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact ggSpRow_recipe_adjoint hp hp2 hpn (le_trans (by norm_num) hlab.2.1) hQ

theorem ggTBJTorusNoncomm_rowR3 (hRig : GGLabelRigidInput) :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR3 p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN y hy hy1 J' hJ' hJl hcount
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hLF : GGInnerDiagOnLabel GGReflSpLabel p Bs L :=
    ggInnerDiagOnLabel_reflSp_of_rowR3 hRig hHyp hL
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGReflSpLabel p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggSpRow_labelAll_adjoint hp hp2 hlab hs))
    (fun _ _ _ _ _ _ hP => hP.1) hLF
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, hr1, hlift, K, _, _, _, e, hpq, hIinn⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      LargeEvenProj (LargeEvenSpGroup K r) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K r)))) e (fun φ hφ => by
    obtain ⟨g, rfl⟩ := hIinn hφ
    exact ⟨e g, by
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  haveI : NeZero r := ⟨by omega⟩
  exact ggTBJ_sp_torusJNoncomm hp hp2 hpq (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB' y hy hJ'
    hcount

theorem ggTBJNaWeylQFourOn_rowR3 (hRig : GGLabelRigidInput) :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR3 p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm (ggTBJTorusNoncomm_rowR3 hRig)

end CFSG.StandardType

end
