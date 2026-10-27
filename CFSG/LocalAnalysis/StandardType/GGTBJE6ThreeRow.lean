module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6Three
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E6Split
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR4Narrow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley TableBExc.E6Three

section E6Three


theorem ggR1E6ThreeRow_labelAll_adjoint {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hpn : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
        (e : R ≃* ↥(adjointGroup Tag.E6 K)), GGTorusLift 3 5 R ∧ 3 ∣ Nat.card K - 1 ∧
          ∀ φ ∈ I, MulAut.congr e φ ∈ (hatAut Tag.E6 K).range := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, K, inferInstance, inferInstance, this,
    TableBExc.recipeEquiv .E6 K, TableBExc.ggTorusLift_E6_three hpq, hpq,
    fun φ hφ => (E6ThreeModel.recipeID_iff_hatAut φ).1 hφ⟩

theorem ggTBJTorusNoncomm_rowR1E6Three (hRig : GGLabelRigidInput) :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ (GGTBRowR1E6 p lab ∧ p = 3) := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN y hy hy1 J' hJ' hJl hcount
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp3 : p = 3 := by
    obtain ⟨-, lab, -, hraw⟩ := hL
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    exact hP.1.2.2
  subst hp3
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hLE : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E6 p lab ∧ p ∣ 2 ^ lab.n - 1) 3 Bs L :=
    ggInnerDiagOnLabel_r1Par_of_rowR1E6 hRig hHyp
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.1, hP.1.2.1⟩, hP.2⟩) hL)
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour 3 lab ∧ GGTBRowR1E6 3 lab ∧ 3 ∣ 2 ^ lab.n - 1)
    (fun lab _ hs => nbrC_labelAll_guard (ggR1E6ThreeRow_labelAll_adjoint hs.2.1 hs.2.2))
    (fun _ _ _ _ _ _ hP => hP.1) hLE
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, K, _, _, _, e, hlift, h3, hIe⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := GGTorusTBGroup.mulEquiv
    (I' := ((hatAut Tag.E6 K).range : Set (MulAut ↥(adjointGroup Tag.E6 K)))) e hIe
    (ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3')
  exact ggTBJ_e6Three_torusNoncomm h3 hTB hy hJ' hJl hcount

theorem ggTBJNaWeylQFourOn_rowR1E6Three (hRig : GGLabelRigidInput) :
    GGTBJRowTarget fun p lab => GGTBRowR1E6 p lab ∧ p = 3 :=
  ggTBJNaWeylQFourOn_of_torusNoncomm (ggTBJTorusNoncomm_rowR1E6Three hRig)

theorem ggTBJNoncommReflOn_of_rowR1E6Three (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧ ¬ (GGTBRowR1E6 p lab ∧ p = 3)) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S (fun p lab => GGTBRowR1E6 p lab ∧ p = 3)
    ((ggTBJNoncommReflOn_of_naWeyl (ggTBJNaWeylQFourOn_rowR1E6Three hRig)).mono
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end E6Three

end CFSG.StandardType

end
