module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPrime
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPsi
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmega
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaMinusEnd
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoConclusion
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LargeExtraspecial.BridgeOrder
public import CFSG.LargeExtraspecial.S14C12RSHolds
public import CFSG.LargeExtraspecial.AS62EnumInputs
public import CFSG.LargeExtraspecial.S14Main
public import Certificates.Certificate19780

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal FrameRoute
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem E6QTwo.marking_cases {L : Subgroup G}
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .D ∧ lab.rank = 4) ∨
        (lab.tag = .twD ∧ lab.rank = 5)) ∧ lab.n = 1)) :
    LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) ∨
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) ∨
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1) := by
  have hlab' : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      (lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) ∨
        ((lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) ∨
          (lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1))) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨h, hn⟩ =>
      h.elim (fun h => Or.inl ⟨h.1, h.2, hn⟩)
        (fun h => Or.inr (h.elim (fun h => Or.inl ⟨h.1, h.2, hn⟩)
          (fun h => Or.inr ⟨h.1, h.2, hn⟩)))) hlab
  rcases largeEvenMarking_label_or hlab' with hU | hDO
  · exact Or.inl hU
  · exact Or.inr (largeEvenMarking_label_or hDO)

theorem GGSecFiveE6QTwoCfg.twistedE6Model_and_ggG0_eq_top
    (hRig : GGLabelRigidInput)
    (hWil : GGTwistedE6MaxElevenInput)
    (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    (hRS : CFSG.LargeExtraspecial.S14.ReifartSmithU62Input)
    (hTP : GGNbrTablePNbrInputOnL GGRegimeN2L)
    (hLB : GGLBalanceInput)
    (hFSE : GGSecFiveE6QTwoFS81Input)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hE6 : GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₆)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .D ∧ lab.rank = 4) ∨
        (lab.tag = .twD ∧ lab.rank = 5)) ∧ lab.n = 1)) :
    ChevalleyExceptionalModel G .twistedE6 2 1 ∧ ggG0 3 B x L D J = ⊤ := by
  have hI : GGThmIHyp 3 B x L := by
    obtain ⟨_, hRC, -⟩ := hC
    exact hRC.1.1.1
  haveI : IsSimpleGroup G := hI.1
  have hG : IsCharTwoType G := hI.2.2.2.1
  rcases E6QTwo.marking_cases hlab with hU | hO | hM
  · obtain ⟨K, _, _, ω, hω, φ, hS, ⟨W, hW, hWb, hn, hr⟩, y, K', hnbr, hK'p, hK'L, hBsLK⟩ :=
      hC.unitaryEnd' hRig hT hE6 hU
    have hGm := hS.chevalleyExceptionalModel hG hW hWb hn hr hT hRS
      (hC.not_nonempty_mulEquiv_psu12 (by rw [hS.card]; norm_num))
    refine ⟨hGm, ggG0_eq_top_of_nbr hWil hGm hI.2.2.1 hnbr ?_
      (Subgroup.isPerfect_iff.mp hS.isPerfect_L) hK'p hK'L hS.elemAbelian hS.card hBsLK hS.mem
      hS.orderOf_b hS.le_centralizer hS.b_not_mem_L⟩
    rw [Nat.card_congr φ.toEquiv]
    exact USixTwo.card_U hS.card_K
  · obtain ⟨y, K', hnbr, hLp, hLK', hBsLK, K, _, _, ω, hω, φ, hS, W, hW, hWb, hn, hr⟩ :=
      hC.orthogonalEnd' hRig hTP hLB hE6 hO
    have hGm := hS.chevalleyExceptionalModel hG hW hWb hn hr hT hRS
      (hC.not_nonempty_mulEquiv_psu12 (by rw [hS.card]; norm_num))
    have hL0 : L ≤ ggG0 3 B x L D J := le_ggG0_left 3 B x L D J
    have hK0 : K' ≤ ggG0 3 B x L D J := le_ggG0_of_ggNbr hnbr
    have hBs0 : Bs ≤ ggG0 3 B x L D J := hBsLK.trans (sup_le hL0 hK0)
    refine ⟨hGm, eq_top_of_maxEleven (hWil G hGm hI.2.2.1) hK0 hL0 hBs0 (hBs0 hS.mem) ?_
      (Subgroup.isPerfect_iff.mp hS.isPerfect_L) hLp hLK' hS.elemAbelian hS.card hS.orderOf_b
      hS.le_centralizer hS.b_not_mem_L⟩
    rw [Nat.card_congr φ.toEquiv]
    exact USixTwo.card_U hS.card_K
  · exact (hC.omegaMinusEnd_false' hFSE hM).elim

theorem ggSecFiveWeylE6QTwoInput_of_bridge
    (hEnd : GGSecFiveE6QTwoEndInput)
    (hFSE : GGSecFiveE6QTwoFS81Input)
    (hTP : GGNbrTablePNbrInputOnL GGRegimeN2L)
    (hLB : GGLBalanceInput) (hRig : GGLabelRigidInput)
    (hWil : GGTwistedE6MaxElevenInput)
    (hT : GGSecFiveE6QTwoTimmesfeldInput)
    (hRS : CFSG.LargeExtraspecial.S14.ReifartSmithU62Input) :
    GGSecFiveWeylE6QTwoInput := by
  intro G _ _ p B Bs x L D J hR hW hE _ _ hC
  have hE6 := hC.weylAt_E6 hE
  obtain rfl := hC.prime_eq_three
  have hlab := hEnd G B Bs x L D J hR (ggSecFiveWeylCase_of_prime_three hR.1 hW) hC
  obtain ⟨hGm, hG0⟩ := hC.twistedE6Model_and_ggG0_eq_top hRig hWil (hT G B Bs x L D J hC) hRS
    hTP hLB hFSE hE6 hlab
  exact ggSecFiveData_of_twistedE6Model hGm hG0

theorem GGSecFiveRouteCfg.exists_sup_eq_of_e6QTwo
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    (hFSE : GGSecFiveE6QTwoFS81Input)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hNS : ¬ GGSplitLie 3 L) {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : ∃ e' : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e')
    (hr : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6)
    (h𝒦 : 𝒦.card = 2)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .D ∧ lab.rank = 4) ∨
        (lab.tag = .twD ∧ lab.rank = 5)) ∧ lab.n = 1)) :
    ∃ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  rcases E6QTwo.marking_cases hlab with hU | hO | hD
  · exact hR.exists_sup_eq_of_twA5 hRig hT hNS e hP hM hr hU
  · exact hR.exists_sup_eq_of_omegaPlus hRig hLB hNS e hP hM hr h𝒦 hO
  · exact ((GGSecFiveE6QTwoCfg.omegaMinusEnd_false' hFSE
      ⟨𝒦, hR, hNS, ι, M, e, hP, hM, hr⟩ hD)).elim

theorem ggSecFiveDataResE6QTwoInput_of_bridge
    (hEnd : GGSecFiveE6QTwoEndInput)
    (hFSE : GGSecFiveE6QTwoFS81Input)
    (hTP : GGNbrTablePNbrInputOnL GGRegimeN2L)
    (hLB : GGLBalanceInput) (hRig : GGLabelRigidInput)
    (hWil : GGTwistedE6MaxElevenInput)
    (hT : GGSecFiveE6QTwoTimmesfeldInput)
    (hRS : CFSG.LargeExtraspecial.S14.ReifartSmithU62Input) :
    GGSecFiveDataResE6QTwoInput := by
  refine ggSecFiveDataResE6QTwoInput_of_e6QTwo
    (ggSecFiveWeylE6QTwoInput_of_bridge hEnd hFSE hTP hLB hRig hWil hT hRS) ?_
  intro G _ _ p B Bs x L D J 𝒦 hR h𝒦 hno hNS ι M e hP hM hr
  have hC : GGSecFiveE6QTwoCfg p B Bs x L D J := ⟨𝒦, hR, hNS, ι, M, e, hP, hM, hr⟩
  obtain rfl := hC.prime_eq_three
  have hlab := hEnd G B Bs x L D J hR.1 (ggSecFiveWeylCase_of_prime_three hR.1.1 hR.2.1) hC
  obtain ⟨K, hK, hA⟩ := hR.exists_sup_eq_of_e6QTwo hRig hLB (hT G B Bs x L D J hC)
    hFSE hNS e hP hM hr h𝒦 hlab
  exact absurd hA (hno K hK)

theorem ggSecFiveE6QTwoTimmesfeldInput_holds :
    GGSecFiveE6QTwoTimmesfeldInput := by
  intro G _ _ B Bs x L D J hC
  have hI : GGThmIHyp 3 B x L := by
    obtain ⟨_, hRC, -⟩ := hC
    exact hRC.1.1.1
  haveI : IsSimpleGroup G := hI.1
  exact CFSG.LargeExtraspecial.Bridge.orderMainFor_of_mainFor
    (CFSG.LargeExtraspecial.S14.mainStatement_of_widthTwo
      CFSG.LargeExtraspecial.S14.aschbacherWidthTwoResidual_holds G)

theorem ggSecFiveDataResE6QTwoInput_of_bridgeInput
    (h : GGSecFiveE6QTwoBridgeInput) (hEnd : GGSecFiveE6QTwoEndInput)
    (hTP : GGNbrTablePNbrInputOnL GGRegimeN2L) (hLB : GGLBalanceInput) (hRig : GGLabelRigidInput) :
    GGSecFiveDataResE6QTwoInput := by
  obtain ⟨hFSE, hWil⟩ := h
  exact ggSecFiveDataResE6QTwoInput_of_bridge hEnd hFSE hTP hLB hRig hWil
    ggSecFiveE6QTwoTimmesfeldInput_holds CFSG.LargeExtraspecial.S14.reifartSmithU62Input_holds

end CFSG.StandardType

end
