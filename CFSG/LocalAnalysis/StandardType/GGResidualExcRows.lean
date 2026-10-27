module

public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Parity
public import Certificates.Certificate709545
public import Certificates.Certificate709548
public import Certificates.Certificate709549
public import Certificates.Certificate709590
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
import CFSG.LocalAnalysis.StandardType.GGNsq2Strict
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGOrthFrameConcl
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6FrameAux
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwE6
import CFSG.Sporadic.Schreier.RuElemAut
import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGTwE6TwoRankOne
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwE6TwoFull
import CFSG.LocalAnalysis.StandardType.GGFrameTBHolds
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueOneOuter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

theorem GGWeylFrame.automizer_le_closure {p : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {ι : Type}
    {M : CoxeterMatrix ι} (h : GGWeylFrame p A M) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤ Subgroup.closure (ggTorusReflSet p A) := by
  obtain ⟨n, hn, hnW, hrefl, e, he⟩ := h
  have hw : ∀ w : M.Group, (e w : MulAut ↥A) ∈ Subgroup.closure (ggTorusReflSet p A) := by
    intro w
    refine (M.toCoxeterSystem).simple_induction
      (p := fun w => (e w : MulAut ↥A) ∈ Subgroup.closure (ggTorusReflSet p A)) w ?_ ?_ ?_
    · intro i
      change (e (M.simple i) : MulAut ↥A) ∈ _
      rw [he i]
      exact Subgroup.subset_closure ⟨n i, hn i, hnW i, rfl, hrefl i⟩
    · change (e 1 : MulAut ↥A) ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · intro x y hx hy
      change (e (x * y) : MulAut ↥A) ∈ _
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
  intro a ha
  have h := hw (e.symm ⟨a, ha⟩)
  rwa [MulEquiv.apply_symm_apply] at h

theorem card_automizerInn_le_ggAutomizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hW : ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma K hN).range)) :
    Nat.card ↥(ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range) ≤
      Nat.card ↥(ggAutomizer K Bs) := by
  classical
  choose c hc hov using exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN hW
  have hcl : Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ} ≤
      ggAutomizer K Bs := (Subgroup.closure_le _).mpr fun φ hφ => hφ.1
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  refine Nat.card_le_card_of_injective (fun a => (⟨c a.1 a.2, hcl (hc a.1 a.2)⟩ : ↥(ggAutomizer K Bs))) ?_
  intro a b hab
  have hcab : c a.1 a.2 = c b.1 b.2 := congrArg Subtype.val hab
  have hb := hov b.1 b.2
  rw [← hcab] at hb
  exact Subtype.ext ((hov a.1 a.2).unique hb)

theorem ggRouteCfg_false_of_card_join_le (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hcard : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) ≤ Nat.card ↥(ggAutomizer X Bs)) : False := by
  rcases hX with hXL | ⟨y, hnb⟩
  · rw [hXL] at hcard
    exact absurd hcard (not_le.mpr (ggPhanStrict_card_lt_join_of_wA hWA hcfg))
  · exact absurd hcard (not_le.mpr (ggPhanStrict_card_lt_join_of_nbr hFix hcfg hnb hXA))

theorem card_ggAutomizerJoin_le_of_weylE {G : Type}
    [Group G] {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (hME : GGIsWeylMatrixE M) :
    Nat.card ↥(ggAutomizerJoin L Bs 𝒦) ≤ 696729600 := by
  rw [← Nat.card_congr e.toEquiv]
  rcases hME with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩
  · exact ((card_coxeterGroup_reindex _ f).trans card_coxeterE6_group).trans_le (by norm_num)
  · exact ((card_coxeterGroup_reindex _ f).trans card_coxeterE7_group).trans_le (by norm_num)
  · exact ((card_coxeterGroup_reindex _ f).trans card_coxeterE8_group).le

section Rows

theorem largeEvenLabelAll_weylFrame_EE8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : ggRowP_EE8 p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGWeylFrame p A (coxeterMatrix (isFiniteType_cartan .E8)) := by
  obtain ⟨htag, hpn⟩ := h
  refine (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inl htag), hpn⟩)
    (ggNEE_largeEvenLabelAll_model_excPlus hp hp2 (Or.inr htag) hpn)).mono fun R _ I _ h => ?_
  refine ⟨_, h.1, fun L' _ _ ψ A hA => ?_⟩
  have hm := h.2 L' ψ A hA
  rw [htag] at hm
  exact ggWTEx1_weylFrame_of_excPlusModel (τ := .E8) hp hp2 hA.2.2.2.2.2.2.2 hm

theorem ggX_card_automizer_ge_of_weylFrame (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    {P : ℕ → LargeEvenLabel → Prop} {ι' : Type} {M' : CoxeterMatrix ι'}
    (hF : ∀ lab, LargeEvenInLambda2 lab → P p lab → LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGWeylFrame p A M')
    (hrow : GGInnerDiagOnLabel P p Bs X) : Nat.card M'.Group ≤ Nat.card ↥(ggAutomizer X Bs) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  obtain ⟨hN, hWF, -⟩ := ggX_exists_overGamma_lift hRig hcfg hX hInn hΛ hhas
    (fun _ _ A => GGWeylFrame p A M') (hF lab hΛ hS)
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.1.1.2.1.2.2.2
  have hlow := card_automizerInn_le_ggAutomizer hp hp2 hBs hSC hN hWF.automizer_le_closure
  obtain ⟨-, -, -, -, e', -⟩ := hWF
  rwa [← Nat.card_congr e'.toEquiv] at hlow

theorem ggX_card_automizer_ge_of_EE8 (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hrow : GGInnerDiagOnLabel ggRowP_EE8 p Bs X) : 696729600 ≤ Nat.card ↥(ggAutomizer X Bs) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  exact NoOffExc.card_weyl_E8.symm.trans_le (ggX_card_automizer_ge_of_weylFrame hRig hcfg hX
    (fun _ _ h => largeEvenLabelAll_weylFrame_EE8 hp hp2 h) hrow)

theorem ggX_card_automizer_ge_of_TwE6Plus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hrow : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs X) : 51840 ≤ Nat.card ↥(ggAutomizer X Bs) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  exact card_coxeterE6_group.symm.trans_le (ggX_card_automizer_ge_of_weylFrame hRig hcfg hX
    (fun _ hΛ h => ggTwE6Row_labelAll_frame hp hp2 hΛ h) hrow)

theorem ggRow_absurd_EE8 (hRig : GGLabelRigidInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (hME : GGIsWeylMatrixE M) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel ggRowP_EE8 p Bs X) : False :=
  ggRouteCfg_false_of_card_join_le hFix hWA hcfg hX hXA
    ((card_ggAutomizerJoin_le_of_weylE e hME).trans (ggX_card_automizer_ge_of_EE8 hRig hcfg hX hrow))

theorem card_ggAutomizerJoin_le_of_E6 {G : Type}
    [Group G] {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (hE6 : ∃ f : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex f) :
    Nat.card ↥(ggAutomizerJoin L Bs 𝒦) ≤ 51840 := by
  rw [← Nat.card_congr e.toEquiv]
  obtain ⟨f, rfl⟩ := hE6
  exact ((card_coxeterGroup_reindex _ f).trans card_coxeterE6_group).le

theorem ggRow_absurd_TwE6Plus_of_E6
    (hRig : GGLabelRigidInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (hE6 : ∃ f : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex f)
    {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs X) : False :=
  ggRouteCfg_false_of_card_join_le hFix hWA hcfg hX hXA
    ((card_ggAutomizerJoin_le_of_E6 e hE6).trans (ggX_card_automizer_ge_of_TwE6Plus hRig hcfg hX hrow))

theorem ggRow_absurd_TwE6_L_of_E6
    (hRig : GGLabelRigidInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (hE6 : ∃ f : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex f)
    (hrow : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) : False := by
  by_cases hp3 : p = 3
  · obtain ⟨w, -⟩ := ggTwE6Bad_weylOfType hcfg.1
      (hrow.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, hp3, hp3 ▸ h.2⟩)
    refine ggRouteCfg_false_of_card_join_le hFix hWA hcfg (Or.inl rfl) le_sup_left
      ((card_ggAutomizerJoin_le_of_E6 e hE6).trans ?_)
    rw [← Nat.card_congr w.toEquiv, card_coxeterE6_group]
  · exact ggRow_absurd_TwE6Plus_of_E6 hRig hFix hWA hcfg e hE6 (Or.inl rfl) le_sup_left
      (hrow.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, h.2, hp3⟩)

theorem ggRow_absurd_TwE6_L_of_E8
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hE8 : ∃ f : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex f) (hrow : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) :
    False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hle : Nat.card ↥Bs ≤ p ^ 7 := by
    by_cases hp3 : p = 3
    · exact NSJoin.nsTwE6Bad_card_le hcfg.1
        (hrow.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, hp3, hp3 ▸ h.2⟩)
    · exact NSJoin.nsTwE6Plus_card_le hcfg.1
        (hrow.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, h.2, hp3⟩)
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
  have hW : GGWeylOfType p CoxeterMatrix.E₈ (ggAutomizerJoin L Bs 𝒦) := by
    obtain ⟨f, rfl⟩ := hE8
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have h8 : p ^ 8 ≤ Nat.card ↥Bs := FrameRoute.pow_le_card_of_weylOfType_of_two hp hp2 hBs hW
    FrameRoute.exists_elemAbelian_two_coxeterE8
  exact absurd (h8.trans hle) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

theorem GGSecFiveRouteCfg.lt_bstar_of_twE6Two_of_not_AD
    (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hLB : GGLBalanceInput)
    (hTCJ : GGTCJKnown) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hA : ¬ GGIsWeylMatrixA M) (hD : ¬ NSJoin.NSTypeD M)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L) : B < Bs :=
  hcfg.lt_bstar_of_twE6Two_typeE hTBF hWI FrameRoute.ggFrameTBNumerologyInput_holds
    FrameRoute.ggFrameTBVacuousInput_holds hRig (ggPumpupInput_of_lBalance hLB) FrameRoute.ggOuterThreeRankInput_holds
    hTCJ hpres (GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 h3 hA hD) hmark

theorem ggRow_absurd_TwE6Two_L
    (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hLB : GGLBalanceInput)
    (hTCJ : GGTCJKnown) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hA : ¬ GGIsWeylMatrixA M) (hD : ¬ NSJoin.NSTypeD M)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L) : False := by
  have hp3 : p = 3 :=
    NSJoin.eq_three_of_innerDiagOnLabel_n_one (ggRouteCfg_prime hcfg).1 (fun _ hl => ⟨hl.2, hl.1.2⟩) hrow
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨htag, -⟩, hn⟩, -⟩ := largeEvenMarking_exists_hasLabel hrow
  have hn1 : ∀ lab', LargeEvenInLambda2 lab' → GGHasLabel lab' (↥L ⧸ Subgroup.center ↥L) → lab'.n = 1 := by
    intro lab' hΛ' hhas'
    have := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hΛ hΛ' hhas hhas') (by rw [htag]; decide)
      (fun ht => by rw [htag] at ht; exact absurd ht (by decide))
    omega
  have hlt := hcfg.lt_bstar_of_twE6Two_of_not_AD hRig hTBF hWI hLB hTCJ hpres h3 hA hD hrow
  obtain ⟨w, hw⟩ := ggTwE6Bad_weylOfType hcfg.1
    (hrow.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1.1, hp3, hp3 ▸ h.1.2⟩)
  obtain ⟨r, hrA, hrR⟩ : ∃ r ∈ ggAutomizer L Bs, GGIsReflection p r :=
    ⟨_, (w (CoxeterMatrix.E₆.simple 0)).2, hw 0⟩
  have hrC := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hrR
  obtain ⟨F, hFf, hFfin, θ, -, hinj, hrange, -, -, -, -, lab', hΛ', hhas', hF⟩ :=
    ggRk1ConclEx_of_twE6Two_L_of_lt hRig hcfg.1.1 hns hrow hlt r hrA hrR
  letI : Field F := hFf
  letI : Finite F := hFfin
  have hcard : Nat.card ↥(ggRankOneIn L Bs r) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← hrange, ← ggSL2_card F]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  exact hbig r hrA hrC (by simp [hcard, hF, hn1 lab' hΛ' hhas'])

theorem ggRow_absurd_TwE6Two
    (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hLB : GGLBalanceInput)
    (hTCJ : GGTCJKnown) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hA : ¬ GGIsWeylMatrixA M) (hD : ¬ NSJoin.NSTypeD M) {X : Subgroup G}
    (hQ4X : X ≠ L → p = 3 → GGInnerDiagOnLabel GGLabQFour p Bs X)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X) : False := by
  by_cases hXL : X = L
  · subst hXL
    exact ggRow_absurd_TwE6Two_L hRig hTBF hWI hLB hTCJ hcfg hns hpres h3 hbig hA hD hrow
  · refine NSJoin.not_innerDiagOnLabel_qFour_of_n_one hRig (fun lab hl => ⟨hl.2, ?_, fun ht => ?_⟩) hrow
      (hQ4X hXL (NSJoin.eq_three_of_innerDiagOnLabel_n_one (ggRouteCfg_prime hcfg).1
        (fun _ hl => ⟨hl.2, hl.1.2⟩) hrow))
    · rw [hl.1.1]
      decide
    · rw [hl.1.1] at ht
      exact absurd ht (by decide)

end Rows

end CFSG.StandardType

end
