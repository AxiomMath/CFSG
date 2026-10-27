module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4ThreeAux
public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclReal
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclCensus
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineTwDTwo
import CFSG.LocalAnalysis.StandardType.GGTBRowF4FrameAux
import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenElt
import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggSecFiveBCoordDExclRestOn_twDTwo :
    GGSecFiveBCoordDExclRestOn fun _ lab => lab.tag = .twD ∧ lab.rank = 2 ∧ lab.n = 1 := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb
    r hr hrefl hsgn hM hLD
  have hp : p.Prime := hR.1.1.tableB_facts.1
  have := Fact.mk hp
  exact (GGResHyp.false_of_twDTwo
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hnb, hR.2.1 y K hnb,
      Or.inr hR.2.1⟩ hM).elim

private theorem open_or_excluded_of_split {p : ℕ} {lab : LargeEvenLabel}
    (hS : GGSecFiveBCoordDExclSplitLabel p lab) (hO : ¬ GGOrthNsSgnLabel p lab) :
    (GGSecFiveBCoordDExclSplitLabel p lab ∧ lab.n = 1 ∧ (lab.tag = .A ∨ lab.tag = .B ∨
      lab.tag = .C ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨ (lab.tag = .twA ∧ lab.rank = 5))) ∨
    (p ≠ 3 ∨ ¬ LargeEvenInLambda2 lab ∨ (lab.n = 1 ∧ lab.tag = .F4) ∨
      (lab.tag = .twD ∧ lab.rank = 2 ∧ lab.n = 1)) := by
  by_cases hp : p = 3
  swap
  · exact Or.inr (Or.inl hp)
  subst hp
  by_cases hΛ : LargeEvenInLambda2 lab
  swap
  · exact Or.inr (Or.inr (Or.inl hΛ))
  obtain ⟨hq, hrow, hcl, hsm⟩ := id hS
  by_cases hF4 : lab.n = 1 ∧ lab.tag = .F4
  · exact Or.inr (Or.inr (Or.inr (Or.inl hF4)))
  by_cases hD2 : lab.tag = .twD ∧ lab.rank = 2 ∧ lab.n = 1
  · exact Or.inr (Or.inr (Or.inr (Or.inr hD2)))
  by_cases hE : lab.n = 1 ∧ (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ (lab.tag = .twA ∧ lab.rank = 5))
  · exact Or.inl ⟨hS, hE.1, Or.inr (Or.inr (Or.inr hE.2))⟩
  have hRes : ¬ (lab.n = 1 ∧ (lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨
      (lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .twD ∧ lab.rank = 2))) := by
    rintro ⟨hn, h | h | h | h | h⟩
    exacts [hF4 ⟨hn, h⟩, hE ⟨hn, Or.inl h⟩, hE ⟨hn, Or.inr (Or.inl h)⟩,
      hE ⟨hn, Or.inr (Or.inr h)⟩, hD2 ⟨h.1, h.2, hn⟩]
  obtain ⟨hn, hABC | hD | hTD⟩ := ggSecFiveBCoordDExcl_census hΛ hq hrow hcl hsm hRes
  · rcases hABC with h | h | h
    · exact Or.inl ⟨hS, hn, Or.inl h⟩
    · exact Or.inl ⟨hS, hn, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨hS, hn, Or.inr (Or.inr (Or.inl h))⟩
  · exact (hO ⟨by norm_num, Or.inl hD.1, by rw [hn]; norm_num,
      (by norm_num : 4 ≤ 5).trans hD.2.2⟩).elim
  · exact (hO ⟨by norm_num, Or.inr hTD.1, by rw [hn]; norm_num, hTD.2.2⟩).elim

theorem ggSecFiveBCoordDExclRestOn_open_of_rows
    (hE6 : GGSecFiveBCoordDExclRestOn fun _ lab => lab.n = 1 ∧ lab.tag = .E6)
    (hTE6 : GGSecFiveBCoordDExclRestOn fun _ lab => lab.n = 1 ∧ lab.tag = .twE6)
    (hTA5 : GGSecFiveBCoordDExclRestOn fun _ lab => lab.n = 1 ∧ lab.tag = .twA ∧ lab.rank = 5)
    (h : GGSecFiveBCoordDExclRestOn fun p lab => GGSecFiveBCoordDExclSplitLabel p lab ∧
      lab.n = 1 ∧ (lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C)) :
    GGSecFiveBCoordDExclRestOn fun p lab => GGSecFiveBCoordDExclSplitLabel p lab ∧ lab.n = 1 ∧
      (lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨
        (lab.tag = .twA ∧ lab.rank = 5)) := by
  refine ggSecFiveBCoordDExclRestOn_of_split (fun _ _ hs => ?_) h
    (ggSecFiveBCoordDExclRestOn_of_split (fun _ _ h => h) hE6
      (ggSecFiveBCoordDExclRestOn_of_split (fun _ _ h => h) hTE6 hTA5))
  obtain ⟨hs, hn, h | h | h | h | h | h⟩ := hs
  exacts [Or.inl ⟨hs, hn, Or.inl h⟩, Or.inl ⟨hs, hn, Or.inr (Or.inl h)⟩,
    Or.inl ⟨hs, hn, Or.inr (Or.inr h)⟩, Or.inr (Or.inl ⟨hn, h⟩),
    Or.inr (Or.inr (Or.inl ⟨hn, h⟩)), Or.inr (Or.inr (Or.inr ⟨hn, h⟩))]

section Certificates


theorem ggTorusWeylFrameW_F4_three
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGTorusWeylFrameW 3 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)
      CoxeterMatrix.F₄ :=
  ggTorusWeylFrameW_of_coordFrameElt Nat.prime_three (by norm_num)
    (TableBF4.idImage_subset_inn K) (TableBF4.center_recipeGroup_eq_bot K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ExcWeylGen.ggTorusWeylGenElt_adjointF4_all Nat.prime_three (by norm_num)))
    (ggTorusCoordFrameElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggWTF4_coordFrameElt_adjointF4 (K := K) Nat.prime_three (by norm_num)))

theorem largeEvenLabelAll_ggTorusWeylFrameW_F4_three (lab : LargeEvenLabel)
    (hF4 : GGF4ThreeLabel 3 lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylFrameW 3 4 R I CoxeterMatrix.F₄ := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, -, -⟩ := hF4
  dsimp only at htag
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusWeylFrameW_F4_three⟩

theorem ggSecFiveBCoordDExclRestOn_f4Two_neighbour
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    (hF4R : GGF4ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp3 : p = 3)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hK𝒦 : K ∈ 𝒦) (hnb : GGNbr p B x D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧ lab.tag = .F4) p Bs K) :
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
  have hS : lab.n = 1 ∧ lab.tag = .F4 := hP.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hP.2.1
  have hF4 : GGF4ThreeLabel 3 lab := ⟨hS.2, rfl, by rw [hS.1]; norm_num⟩
  obtain ⟨R', _, θ', I', F', hBsI', hFrame'⟩ := exists_innerDiagDatum_of_labelAll hRig hInnK
    hlab hhas (largeEvenLabelAll_ggTorusWeylFrameW_F4_three lab hF4) hN
  have hM' : LargeEvenMarking ↥K (fun lab _ _ I _ θ => GGF4ThreeLabel 3 lab ∧
      Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hP =>
      ⟨⟨hP.1.2, rfl, by rw [hP.1.1]; norm_num⟩, hP.2.1, hP.2.2⟩) hM
  have hSCent : GGTorusSelfCent 3 (ggGamma K hN).range := ggTorusSelfCent_ggGamma hN hSC
  have hr : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    hF4R G 3 B Bs x L D J hcfg hNoTr rfl y K hnb hM' hN hSCent
  have hTB : GGTorusTBGroup 3 4 R' I' K (ggQuotHom θ') (ggGamma K hN).range :=
    ggTorusTBGroup_of_nbr_card hcfg (by norm_num) hnb hInnK.1 θ' hN hBsI' hr
  have hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 :=
    ggNbr_card_center_le_of_centerPCyclic hcyc hcfg hInnK
  have hW : GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer K Bs) :=
    ggWeylOfType_of_frame hp hp2 hBs hSC hNoTr hN hZ (hFrame' K (ggQuotHom θ') _ hTB)
  exact map_le_coordProdStab_of_weylOfType_noFour hp hp2 coxeterMatrixF₄_noFour hW eta
    (map_ggAutomizer_le_bSignedFull_of_join hK𝒦 eta hK)

theorem ggSecFiveBCoordDExclRestOn_f4Two
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    (hF4R : GGF4ThreeNbrRankInput) :
    GGSecFiveBCoordDExclRestOn (fun _ lab => lab.n = 1 ∧ lab.tag = .F4) := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn hM hLD
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hIncl :=
    ggSecFiveBCoordDExclRestOn_f4Two_neighbour hRig hcyc hF4R hR rfl eta hK hK𝒦 hnb hM
  rcases hsgn with ⟨i, hri⟩
  exact false_of_sgnAut_mem_map_coordProdStab (by norm_num) (by norm_num) eta hr hri hIncl

private theorem ggSecFiveBCoordDExclRestOn_excluded (hRig : GGLabelRigidInput)
    (hcyc : GGLabelCenterPCyclicInput) (hF4R : GGF4ThreeNbrRankInput) :
    GGSecFiveBCoordDExclRestOn fun p lab => p ≠ 3 ∨ ¬ LargeEvenInLambda2 lab ∨
      (lab.n = 1 ∧ lab.tag = .F4) ∨ (lab.tag = .twD ∧ lab.rank = 2 ∧ lab.n = 1) := by
  refine ggSecFiveBCoordDExclRestOn_of_split (fun _ _ h => h)
    ggSecFiveBCoordDExclRestOn_ne_three ?_
  refine ggSecFiveBCoordDExclRestOn_of_split (fun _ _ h => h)
    ggSecFiveBCoordDExclRestOn_not_lambda2 ?_
  exact ggSecFiveBCoordDExclRestOn_of_split (fun _ _ h => h)
    (ggSecFiveBCoordDExclRestOn_f4Two hRig hcyc hF4R) ggSecFiveBCoordDExclRestOn_twDTwo

theorem ggSecFiveBCoordDExclRestOn_split_of_open (hRig : GGLabelRigidInput)
    (hcyc : GGLabelCenterPCyclicInput) (hF4R : GGF4ThreeNbrRankInput)
    (h : GGSecFiveBCoordDExclRestOn fun p lab => GGSecFiveBCoordDExclSplitLabel p lab ∧
      lab.n = 1 ∧ (lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .E6 ∨
        lab.tag = .twE6 ∨ (lab.tag = .twA ∧ lab.rank = 5))) :
    GGSecFiveBCoordDExclRestOn fun p lab =>
      GGSecFiveBCoordDExclSplitLabel p lab ∧ ¬ GGOrthNsSgnLabel p lab :=
  ggSecFiveBCoordDExclRestOn_of_split (fun _ _ hs => open_or_excluded_of_split hs.1 hs.2) h
    (ggSecFiveBCoordDExclRestOn_excluded hRig hcyc hF4R)

end Certificates

end CFSG.StandardType

end
