module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeE6TwoAux
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclCensus
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Certificates


theorem ggTorusWeylFrameW_E6Two_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusWeylFrameW 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)
      CoxeterMatrix.F₄ := by
  have instCharP : CharP K 2 :=
    charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  have hModel : GGExcPlusWeylModelSCr .F4 3 4 (TableBExc.RecipeGroup .E6 K)
      (TableBExc.RecipeID .E6 K) :=
    ggExcPlusWeylModelSCr_of_frameModelOn Nat.prime_three
      (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
      (ggCenterPrime_recipe_E6_two hK Nat.prime_three)
      ((excPlusFrameModelOn_E6Two_three hK).of_mulEquiv (TableBExc.recipeEquiv .E6 K))
  rw [FrameRoute.coxeterF4_eq]
  exact fun L' _ _ ψ A hA =>
    ggWTEx1_weylFrame_of_excPlusModel Nat.prime_three (by norm_num) hA.2.2.2.2.2.2.2
      (hModel L' ψ A hA)

theorem largeEvenLabelAll_E6Two_three_liftFrame {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift 3 4 R ∧ GGTorusWeylFrameW 3 4 R I CoxeterMatrix.F₄ := by
  have hW : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusWeylFrameW 3 4 R I CoxeterMatrix.F₄ := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨htag, hn1⟩ := h
    dsimp only at htag hn1
    subst htag
    subst hn1
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusWeylFrameW_E6Two_three (by rw [hK]; rfl)⟩
  exact largeEvenLabelAll_and (largeEvenLabelAll_torusLift_E6_two h) hW

theorem ggSecFiveBCoordDExclRestOn_e6Two_neighbour
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp3 : p = 3)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hK𝒦 : K ∈ 𝒦) (hnb : GGNbr p B x D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧ lab.tag = .E6) p Bs K) :
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
  subst hp3
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  have hp : (3 : ℕ).Prime := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hBs : IsElemAbelian 3 Bs := hcfg.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNoTr : GGNoTransvection 3 Bs := hR.1.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hM
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  have hS : lab.n = 1 ∧ lab.tag = .E6 := hP.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hP.2.1
  have hFrameAll : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift 3 4 R ∧ GGTorusWeylFrameW 3 4 R I CoxeterMatrix.F₄ :=
    largeEvenLabelAll_E6Two_three_liftFrame ⟨hS.2, hS.1⟩
  obtain ⟨R', _, θ', I', F', hBsI', hlift', hFrame'⟩ :=
    exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas hFrameAll hN
  have hTB : GGTorusTBGroup 3 4 R' I' K (ggQuotHom θ') (ggGamma K hN).range :=
    ggTorusTBGroup_of_nbr hcfg hnb hInnK.1 θ' hN hBsI' hlift'
  have hF : GGWeylFrame 3 (ggGamma K hN).range CoxeterMatrix.F₄ :=
    hFrame' K (ggQuotHom θ') (ggGamma K hN).range hTB
  have hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 :=
    ggNbr_card_center_le_of_centerPCyclic hcyc hcfg hInnK
  have hW : GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer K Bs) :=
    ggWeylOfType_of_frame hp hp2 hBs hSC hNoTr hN hZ hF
  have hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n 3 :=
    map_ggAutomizer_le_bSignedFull_of_join hK𝒦 eta hK
  exact map_le_coordProdStab_of_weylOfType_noFour hp hp2 coxeterMatrixF₄_noFour hW eta hAK

theorem ggSecFiveBCoordDExclRestOn_e6Two
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput) :
    GGSecFiveBCoordDExclRestOn (fun _ lab => lab.n = 1 ∧ lab.tag = .E6) := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn hM hLD
  subst hp3
  have hIncl :=
    ggSecFiveBCoordDExclRestOn_e6Two_neighbour hRig hcyc hR rfl eta hK hK𝒦 hnb hM
  rcases hsgn with ⟨i, hri⟩
  exact false_of_sgnAut_mem_map_coordProdStab (by norm_num) (by norm_num) eta hr hri hIncl

end Certificates

end CFSG.StandardType

end
