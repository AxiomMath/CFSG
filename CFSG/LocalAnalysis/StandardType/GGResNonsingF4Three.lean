module

public import CFSG.LocalAnalysis.StandardType.GGResJTwE6Lagrange
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
import CFSG.LocalAnalysis.StandardType.GGResRowF4ThreeOn
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4ThreeAux
import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

section Frame


theorem largeEvenLabelAll_weylFrameW_F4_three {lab : LargeEvenLabel} (h : lab.tag = .F4) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylFrameW 3 4 R I CoxeterMatrix.F₄ := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h
  subst h
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggWTF4_weylFrameW_F4_three⟩

theorem card_ggAutomizer_of_f4Three {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) {X : Subgroup G}
    (hX : GGInnerDiagOnLabel GGF4ThreeLabel p Bs X)
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p) :
    Nat.card ↥(ggAutomizer X Bs) = 1152 := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hM := largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .F4)
    (P' := fun R _ I _ => GGTorusWeylFrameW 3 4 R I CoxeterMatrix.F₄)
    (fun _ _ h => largeEvenLabelAll_weylFrameW_F4_three h) (fun _ _ _ _ _ _ hP => hP.1.1) hX
  obtain ⟨hperf, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hp3, -⟩, hN, hind⟩, hF⟩ := largeEvenRawDatum_exists hraw
  subst hp3
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have hTB := ggTorusTBGroup_of_card hcfg (by norm_num) hperf θ hN hBsI
    (ggF4Three_rank_of_innerDiagOnLabel hcfg hNoTr hX hN)
  exact ggF4Orig_card_weylOfType_F4 (ggWeylOfType_of_frame hp hp2 hBs hSC hNoTr hN hZ
    (hF ↥X (ggQuotHom θ) (ggGamma X hN).range hTB))

theorem GGResHyp.nonsingAut_of_f4Three {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {X : Subgroup G}
    (hX : GGInnerDiagOnLabel GGF4ThreeLabel p Bs X)
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p) :
    GGResNonsingAut p Bs X := by
  refine ⟨?_, fun _ _ _ _ _ => ?_⟩
  · rw [card_ggAutomizer_of_f4Three hH.1 hH.2.2.2.1 hX hZ]
    rintro (⟨k, -, -, hk⟩ | ⟨-, h⟩)
    · exact factorial_succ_ne_of_between (a := 6) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) hk.symm
    · norm_num at h
  · obtain ⟨lab, hΛ, hhas, _, _, _, _, _, ⟨htag, -, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hX
    refine ⟨lab, hΛ, hhas, ggTwE6ThreeFreeLabel_of_two_adic hΛ ?_⟩
    obtain ⟨t, k, n⟩ := lab
    dsimp only at htag ⊢
    subst htag
    show padicValNat 2 (ordF4 (2 ^ n)) ≤ 30 * n
    rw [padicValNat_ordF4 (f := n) rfl hΛ.1]
    omega

end Frame

section Exclusion


theorem ggResExact3_false_of_f4Three_L (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hP : GGStdSubPrimeInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J) (hL : GGInnerDiagOnLabel GGF4ThreeLabel p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False :=
  ggResExact3_false_of_nonsingAut_L hT hLift hTCJ hRig hP hH hJ
    (hH.nonsingAut_of_f4Three hL (card_bstar_inf_center_le hH.1)) hD

theorem ggResExact3_false_of_f4Three_K (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hcyc : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J) (hK : GGInnerDiagOnLabel GGF4ThreeLabel p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False :=
  ggResExact3_false_of_nonsingAut_K hT hLift hTCJ hRig hLB hP hH hJ
    (hH.nonsingAut_of_f4Three hK
      (ggNbr_card_center_le_of_centerPCyclic hcyc hH.1 (hH.2.2.1.2 y K hH.2.2.2.2.1))) hD

end Exclusion

end CFSG.StandardType

end
