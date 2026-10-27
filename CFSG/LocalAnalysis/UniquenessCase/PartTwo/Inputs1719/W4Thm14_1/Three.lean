module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.SimpleGen2
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.CGT.PushingUpLit.BHS.FourOne
public import CFSG.CGT.PushingUpLit.BHS.FourOneD
public import CFSG.CGT.PushingUpLit.BHS.HomTransfer
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GroupTheory.StronglyClosedTI.OddCore
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.UEqZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.Quasithin.Background.B69Main
public import CFSG.Quasithin.Background.B69Struct
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124Core
public import CFSG.Quasithin.Background.C124L2PClass
public import CFSG.Quasithin.Background.C124Star
public import CFSG.Quasithin.Background.C124Z3Class
public import CFSG.Quasithin.Background.C126A5Core4
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.F918V3QB1
public import CFSG.Quasithin.Background.RonanH143Main
public import CFSG.Quasithin.Background.SmithA36
public import CFSG.Quasithin.H13.A6S13821zz10
public import CFSG.Quasithin.H13.A6S13821zz3
public import CFSG.Quasithin.H13.A6S13821zz4
public import CFSG.Quasithin.H13.A6S13821zz9
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
import CFSG.Quasithin.Background.RonanE114Pair
import CFSG.Quasithin.Vol2.Ch11SecU1Crit
import CFSG.Quasithin.Vol2.Ch11SecU1Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w4Thm14_1_three (hK141 : K141MultSpace) (hKGL : KGL42Seven)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L H M : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hcomp : IsComponentOf L Y) (hL3 : IsL3 ↥L 1)
    (hH : H = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV H = ⊥)
    (hnorm : normIn Y L = L ⊔ M) (hM : M = centGroupIn Y L) (hm : E3.mParam Y = 4)
    (h2 : ∀ g : MulAut W, g ∈ Y → g ∉ normIn Y L →
      commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥)
    (hV : commSub (⊤ : Subgroup W) L = ⊤) :
    IsSubgroupOfAlt ↥M 8 ∧ (7 ∣ Nat.card M → (IsAlt ↥M 7 ∨ IsAlt ↥M 8 ∨ IsL3 ↥M 1)) ∧
      (IsL3 ↥M 1 → fixV M ≠ ⊥) := by
  classical
  have hcardL : Nat.card ↥L = 168 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL3
  have hLne : L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardL
    omega
  have hYnorm : Y ≤ normIn Y L := by
    intro g hg
    by_contra hgn
    have hbot := h2 g hg hgn
    rw [hV] at hbot
    have hmapeq : L.map (MulAut.conj g).toMonoidHom = ⊥ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Lin_eq_bot_of_commSub_top_eq_bot hbot
    have hcard := Subgroup.card_map_of_injective (K := L)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hmapeq, Subgroup.card_bot] at hcard
    omega
  have hnormEq : normIn Y L = Y := le_antisymm inf_le_left hYnorm
  have hYLM : Y = L ⊔ M := by rw [← hnorm, hnormEq]
  have hLY : L ≤ Y := by rw [hYLM]; exact le_sup_left
  have hLnormY : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr fun g hg => (hYnorm hg).2
  have hHmap : ∀ g ∈ Y, L.map (MulAut.conj g).toMonoidHom = L := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYnorm hg).2
  have hHL : H = L := by
    rw [hH]
    refine le_antisymm (iSup₂_le fun g hg => le_of_eq (hHmap g hg)) ?_
    refine le_iSup₂_of_le (1 : MulAut W) (Y.one_mem) ?_
    have hcone : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
      ext x
      simp [MulAut.conj_apply]
    rw [hcone, Subgroup.map_id]
  have hfixL : fixV L = ⊥ := hHL ▸ hfix
  have hIrr : IrrSpanTrans Y L := by
    have h125 := w4Lem12_5_holds (W := W) hW Y hO2 hB L hLne hLY hLnormY
    exact (h125.2 L hcomp (hHL.symm.trans hH)).1
  have hK := hK141 (W := W) hW Y L M hL3 hLY hM hYLM hfixL hIrr hB hm
  rcases hK with hMbot | ⟨U, hU, hMU, hfaith, hBM⟩
  ·
    subst hMbot
    have hAltBot : IsSubgroupOfAlt ↥(⊥ : Subgroup (MulAut W)) 8 := by
      haveI : Unique ↥(⊥ : Subgroup (MulAut W)) :=
        ⟨⟨1⟩, fun a => Subtype.ext (Subgroup.mem_bot.mp a.2)⟩
      haveI : Unique ↥(⊥ : Subgroup (alternatingGroup (Fin 8))) :=
        ⟨⟨1⟩, fun a => Subtype.ext (Subgroup.mem_bot.mp a.2)⟩
      exact ⟨⊥, ⟨MulEquiv.ofUnique⟩⟩
    refine ⟨hAltBot, ?_, ?_⟩
    · intro h7
      rw [Subgroup.card_bot] at h7
      exact absurd h7 (by norm_num)
    · intro hL3bot
      have h168 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL3bot
      rw [Subgroup.card_bot] at h168
      omega
  ·
    have hMY : M ≤ Y := by rw [hM]; exact inf_le_left
    have hMn : (M.subgroupOf Y).Normal := by
      refine Subgroup.Normal.mk ?_
      intro c hc g
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      have hcY : (c : MulAut W) ∈ Y := c.2
      have hcM : (c : MulAut W) ∈ M := hc
      have hcC : (c : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
        rw [hM] at hcM
        exact (Subgroup.mem_inf.mp hcM).2
      change (g : MulAut W) * (c : MulAut W) * (g : MulAut W)⁻¹ ∈ M
      rw [hM]
      refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem g.2 hcY) (Y.inv_mem g.2), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hx' : (g : MulAut W)⁻¹ * x * (g : MulAut W) ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hYnorm (Y.inv_mem g.2)).2 x).mp hx
      have hcomm : ((g : MulAut W)⁻¹ * x * (g : MulAut W)) * (c : MulAut W) =
          (c : MulAut W) * ((g : MulAut W)⁻¹ * x * (g : MulAut W)) :=
        Subgroup.mem_centralizer_iff.mp hcC _ hx'
      calc x * ((g : MulAut W) * (c : MulAut W) * (g : MulAut W)⁻¹)
          = (g : MulAut W) * (((g : MulAut W)⁻¹ * x * (g : MulAut W)) * (c : MulAut W)) *
              (g : MulAut W)⁻¹ := by group
        _ = (g : MulAut W) * ((c : MulAut W) * ((g : MulAut W)⁻¹ * x * (g : MulAut W))) *
              (g : MulAut W)⁻¹ := by rw [hcomm]
        _ = ((g : MulAut W) * (c : MulAut W) * (g : MulAut W)⁻¹) * x := by group
    have hO2M : O2Trivial M :=
      CFSG.GroupTheory.o2Trivial_of_normal hO2 hMY hMn
    let e := autSubEquivOfFaithful hMU hfaith
    have hO2aut : O2Trivial (autSub M U) := by
      intro P hP hPn hP2
      let N : Subgroup ↥(autSub M U) := P.subgroupOf (autSub M U)
      have hN2 : IsPGroup 2 N := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm
      let Q' : Subgroup ↥M := N.map e.symm.toMonoidHom
      have hQ'n : Q'.Normal := hPn.map e.symm.toMonoidHom e.symm.surjective
      have hQ'2 : IsPGroup 2 Q' := IsPGroup.map (p := 2) (H := N) hN2 e.symm.toMonoidHom
      let Q : Subgroup (MulAut W) := Q'.map M.subtype
      have hQM : Q ≤ M := by rintro _ ⟨q, -, rfl⟩; exact q.2
      have hQn : (Q.subgroupOf M).Normal := by
        have hEq : Q.subgroupOf M = Q' := by
          ext x
          constructor
          · intro hx
            rw [Subgroup.mem_subgroupOf] at hx
            obtain ⟨q, hq, hqe⟩ := hx
            have hqx : q = x := Subtype.ext hqe
            exact hqx ▸ hq
          · intro hx
            exact Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
        rw [hEq]
        exact hQ'n
      have hQ2 : IsPGroup 2 Q := IsPGroup.map (p := 2) (H := Q') hQ'2 M.subtype
      have hQbot : Q = ⊥ := hO2M Q hQM hQn hQ2
      refine (Subgroup.eq_bot_iff_forall P).2 fun p hp => ?_
      have hpU : (⟨p, hP hp⟩ : ↥(autSub M U)) ∈ N := Subgroup.mem_subgroupOf.mpr hp
      have hmem' : e.symm ⟨p, hP hp⟩ ∈ Q' :=
        Subgroup.mem_map_of_mem e.symm.toMonoidHom hpU
      have hmemQ : ((e.symm ⟨p, hP hp⟩ : ↥M) : MulAut W) ∈ Q := ⟨_, hmem', rfl⟩
      rw [hQbot] at hmemQ
      have h1 : e.symm ⟨p, hP hp⟩ = 1 := Subtype.ext (Subgroup.mem_bot.mp hmemQ)
      have h2 : (⟨p, hP hp⟩ : ↥(autSub M U)) = 1 := by
        have := congrArg e h1
        simpa using this
      simpa using congrArg Subtype.val h2
    have hAutCard : Nat.card ↥M = Nat.card ↥(autSub M U) := Nat.card_congr e.toEquiv
    have hFixle : (fixV (autSub M U)).map U.subtype ≤ fixV M := by
      rintro u ⟨u', hu', rfl⟩
      have hu'' : u' ∈ fixV (autSub M U) := hu'
      rw [mem_fixV] at hu'' ⊢
      intro m hm
      have hmem : resHom U ⟨m, hMU hm⟩ ∈ autSub M U := by
        rw [mem_autSub]
        exact ⟨⟨m, hMU hm⟩, hm, rfl⟩
      have h1 := hu'' (resHom U ⟨m, hMU hm⟩) hmem
      have h2 := congrArg (fun x : ↥U => (x : W)) h1
      simpa [resHom_apply] using h2
    have hFixne : fixV (autSub M U) ≠ ⊥ → fixV M ≠ ⊥ := by
      intro hne hbot
      apply hne
      have hmapbot : (fixV (autSub M U)).map U.subtype = ⊥ :=
        le_bot_iff.mp (hbot ▸ hFixle)
      exact (Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp hmapbot
    have hKGLfull : ∀ _ : 7 ∣ Nat.card M,
        IsAlt ↥M 7 ∨ IsAlt ↥M 8 ∨ (IsL3 ↥M 1 ∧ fixV M ≠ ⊥) := by
      intro h7
      have h7' : 7 ∣ Nat.card ↥(autSub M U) := by rw [← hAutCard]; exact h7
      have hWU : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hW (u : W))
      rcases hKGL (U := ↥U) hWU hU (autSub M U) hO2aut hBM h7' with hA7 | hA8 | ⟨hL3', hfixU⟩
      · exact Or.inl ⟨e.trans hA7.some⟩
      · exact Or.inr (Or.inl ⟨e.trans hA8.some⟩)
      · exact Or.inr (Or.inr ⟨LieModel.of_mulEquiv e.symm hL3', hFixne hfixU⟩)
    refine ⟨isSubgroupOfAlt_eight_of_faithful hW hU hMU hfaith, ?_, ?_⟩
    · intro h7
      rcases hKGLfull h7 with hA7 | hA8 | ⟨hL3M, -⟩
      · exact Or.inl hA7
      · exact Or.inr (Or.inl hA8)
      · exact Or.inr (Or.inr hL3M)
    · intro hL3M
      have h7M : 7 ∣ Nat.card M := by
        rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL3M]
        norm_num
      rcases hKGLfull h7M with hA7 | hA8 | ⟨-, hfixM⟩
      · exfalso
        have hc : Nat.card ↥M = 2520 := by
          rw [Nat.card_congr hA7.some.toEquiv, nat_card_alternatingGroup]
          norm_num
        rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL3M] at hc
        norm_num at hc
      · exfalso
        have hc : Nat.card ↥M = 20160 := by
          rw [Nat.card_congr hA8.some.toEquiv, nat_card_alternatingGroup]
          norm_num
        rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL3M] at hc
        norm_num at hc
      · exact hfixM

theorem w4Thm14_1Used_of_kfacts (hKL : KL32PairRank) (hKI : KInvolGen)
    (hK141 : K141MultSpace) (hKGL : KGL42Seven) : W4Thm14_1Used := by
  intro W _ _ hW Y L H M _ hO2 hB hcomp hL3 hH hfix hnorm hM hm
  have h2 := w4Thm14_1_two hKL hKI kSimpleGen2_holds hW hO2 hB hcomp hL3 hH hfix hm
  exact ⟨h2, fun hV =>
    w4Thm14_1_three hK141 hKGL hW hO2 hB hcomp hL3 hH hfix hnorm hM hm h2 hV⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
