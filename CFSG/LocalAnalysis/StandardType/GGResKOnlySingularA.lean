module

public import CFSG.LocalAnalysis.StandardType.GGResSingularAExactTwo
public import CFSG.LocalAnalysis.StandardType.GGResThreeSettled
public import CFSG.LocalAnalysis.StandardType.GGK2E6ExactTwoJoin
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeBLinearNs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.K_only_singularA_exact2_weyl_join
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) [Fact p.Prime]
    (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K)
    (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hcard : GGResLeviDatumCard 2 p Bs K J L ggSelAny (ggTypLADvd p))
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3 : ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny))
    (hreserved : ¬ ggReservedRows p J L K)
    (htwo : ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K))
    (hC2 : ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K))
    (hSU2 : ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hTBF : GGTBFixInput := ggTBFixInput_holds
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hLift : GGTBTorLiftRows := ggTBTorLiftRows_holds
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput := ggRawInndiagIsoInput_of_rest
    (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  have hTCJ : GGTCJKnown := TCJ.ggTCJKnown_holds
  have hI3 : GGNbrSubcomponentInput := ggNbrSubcomponentInput_proved
  have hLB : GGLBalanceInput := ggLBalanceInput_of_catalogueSchreier
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny :=
    fun h => hno3 (Or.inl h)
  have hnoRowK : ¬ GGResRowAt ggRowTwoNode p J K := fun h => htwo (Or.inr h)
  obtain ⟨hp3, hcase⟩ := hH.K_only_exact2_actual_classification_three
    hTBF hT hLift hD hno2L hno3L hnoRowK hRig hraw hiso hTCJ hI3 hLB
  subst hp3
  rcases hcase with hTor | hRes
  · exact hH.K_only_E6_exact2_weyl_join hTor.2 (not_or.mpr ⟨hno2L, hno3L⟩)
  have hsing := GGResLeviDatumCard.singular_card (Or.inl hcard)
  obtain ⟨n, -, -, hfac⟩ := hcard.card_eq_factorial_of_typLADvd
  have hne1152 : Nat.card (ggAutomizer K Bs) ≠ 1152 := by
    intro hc
    exact factorial_succ_ne_of_between (a := 6) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) (hfac.symm.trans hc)
  have hne51840 : Nat.card (ggAutomizer K Bs) ≠ 51840 := by
    intro hc
    exact factorial_succ_ne_of_between (a := 8) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) (hfac.symm.trans hc)
  have hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 :=
    ggNbr_card_center_le_of_centerPCyclic ggLabelCenterPCyclicInput_holds hH.1
      (hH.2.2.1.2 y K hH.2.2.2.2.1)
  have hMark : GGInnerDiagOnLabel (fun _ lab =>
      (lab.tag = .A ∧ lab.n = 1) ∨ GGF4ThreeLabel 3 lab ∨
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)) 3 Bs K :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
      rcases h.2 with hA | hF4 | hE6 | hTw | hBad
      · exact Or.inl ⟨hA.1, hA.2.2.1⟩
      · exact Or.inr (Or.inl hF4)
      · refine Or.inr (Or.inr (Or.inl ⟨hE6.1, ?_⟩))
        rw [hE6.2.1]
        norm_num
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hTw.1, hTw.2.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hBad.1, hBad.2.2⟩)))) hRes
  rcases hMark.elim_or with hA | hRest
  · exact (hH.not_ggSingularWeylOrder_K_of_linearNs ggLabelCenterPCyclicInput_holds
      (fun lab h => by
        refine ⟨h.1, ?_⟩
        rw [h.2]
        norm_num) hA hsing).elim
  rcases hRest.elim_or with hF4 | hRest
  · exact (hne1152 (card_ggAutomizer_of_f4Three hH.1 hH.2.2.2.1 hF4 hZ)).elim
  rcases hRest.elim_or with hE6 | hRest
  · exact (hne1152 (ggRelativeF4_actual_side_card_and_rank hH (Or.inr rfl) hE6
      (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_E6Plus hlab hs)).1).elim
  rcases hRest.elim_or with hTw | hBad
  · exact (hne1152 (ggRelativeF4_actual_side_card_and_rank hH (Or.inr rfl) hTw
      (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_twE6Dvd hlab hs)).1).elim
  obtain ⟨labK, hΛK, hHasK, R0, _, I0, F0, θ0, hPK⟩ :=
    largeEvenMarking_exists_hasLabel hBad
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hPK.2.1
  have hbadLab : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    largeEvenMarking_mono (fun lab _ _ I _ θ hP => by
      obtain ⟨t, r, en⟩ := lab
      obtain ⟨rfl, hdvd⟩ := hP.1
      exact ⟨⟨rfl, rfl, hdvd⟩,
        Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, hdvd⟩),
        hP.2.1, hP.2.2⟩) hBad
  have hsc : GGTorusSelfCent 3 (ggGamma K hN).range :=
    ggTorusSelfCent_ggGamma hN hH.1.2.1.2.2.2
  have hcard5 : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
    ggTwE6ThreeNbrRankInput_holds G 3 B Bs x L D J hH.1 rfl y K
      hH.2.2.2.2.1 hbadLab hN hsc
  obtain ⟨eK, -⟩ := hH.weylOfType_E6_of_card_gamma_five hRig hΛK hHasK
    (Or.inr ⟨hPK.1.1, hPK.1.2⟩) hN hcard5
  exact (hne51840 ((Nat.card_congr eK.toEquiv).symm.trans l05nQW_ord_coxeterE6)).elim

theorem ggResMultiNodeRestTwoOnlyOutsideRowsInput_of_L
    (hL : GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
      ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
        GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)) :
    GGResMultiNodeRestTwoOnlyOutsideRowsInput := by
  classical
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE
    ⟨hD, hno3, hreserved, htwo, hC2, hSU2⟩
  by_cases hDL : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny
  · exact hL G p B Bs x L D J y K hH hF hS hE
      ⟨hDL, hno3, hreserved, htwo, hC2, hSU2⟩
  have hDK := hD.resolve_left hDL
  rcases ggResExact2_K_reverse_or_singular ggTBFixInput_holds hH hDK with
      (hrev | hrev) | hA | ⟨hp3, hE6⟩
  · exact (hDL hrev).elim
  · exact (hno3 (Or.inl hrev)).elim
  · exact hH.K_only_singularA_exact2_weyl_join hF hS hE hDK hA hDL
      hno3 hreserved htwo hC2 hSU2
  · subst hp3
    exact hH.K_only_E6_exact2_weyl_join hE6
      (not_or.mpr ⟨hDL, fun h => hno3 (Or.inl h)⟩)

end CFSG.StandardType
