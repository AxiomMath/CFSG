module

public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724
public import Certificates.Certificate709545
public import Certificates.Certificate709548
public import Certificates.Certificate709549
public import Certificates.Certificate709590
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGMemberE7TwoRankOne
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrInputs
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryGen
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
import CFSG.LocalAnalysis.StandardType.ExcPay.RouteE7Three
import CFSG.LocalAnalysis.StandardType.ExcPay.TwE6
import CFSG.LocalAnalysis.StandardType.GGResidualGenTwE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

section Proofs


theorem ggResGen_exists_act {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) : ∃ b : ↥Bs, ggGamma X hN b ≠ 1 := by
  rcases hX with rfl | ⟨⟨y, hnb⟩, -⟩
  · exact ggGamma_L_exists_ne_one hcfg.1.1 hN
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have h3 := pow_three_le_card_range_ggGamma_bstar hcfg.1.1 hnb hN
  by_contra hall
  have hbot : (ggGamma X hN).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_bot]
    by_contra hb
    exact hall ⟨b, hb⟩
  rw [hbot, Subgroup.card_bot] at h3
  have h1 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
  omega

theorem ggResGenFrame_of_not_rest
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (hnsX : ¬ GGSplitLie p X) (hXU : ¬ GGMemberUnitary p Bs X)
    (hrest : ¬ GGInnerDiagOnLabel ggRowP_ResGenRest p Bs X) :
    ∃ Φ : OrthTorus.OrthWeakFrame p Bs X, Φ.Recognized := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  haveI : Fact p.Prime := ⟨hp⟩
  have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hX with rfl | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hw.2
  have h4 : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) ∨
      (ggRowP_NF4 p lab ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨ ggRowP_ResGenRest p lab) p Bs X := by
    refine (ggX_ennola_of_nonSplit hcfg hpres h3 hX hnsX).mono_label_of_hasLabel fun lab hΛ _ h => ?_
    have hn1 : 1 ≤ lab.n := hΛ.1
    rcases h with (hESU | hOmP | hOmM | hTw | hE7 | hE8) | hF4
    · by_cases hc : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc.1, Or.inl ⟨hESU, hc.2⟩⟩)))))
      · exact Or.inl ⟨hESU, hc⟩
    · by_cases hn : 2 ≤ lab.n
      · exact Or.inr (Or.inl ⟨Or.inl hOmP, hn⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, Or.inr (Or.inl hOmP)⟩)))))
    · by_cases hn : 2 ≤ lab.n
      · exact Or.inr (Or.inl ⟨Or.inr hOmM, hn⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, Or.inr (Or.inr hOmM)⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hTw)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE8)))))
    · exact Or.inr (Or.inr (Or.inl hF4))
  rcases GGInnerDiagOnLabel.elim_or
      (S := fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) h4 with h | h
  · exact absurd h hXU
  rcases GGInnerDiagOnLabel.elim_or
      (S := fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) h with h | h
  ·
    exact OrthTorus.exists_orthWeakFrame_of_marking ggLabelRigidInput_holds hp2 hcfg.1.1.2.1.2.1
      hcfg.1.1.2.1.2.2.2 h (ggResGen_exists_act hcfg hX)
  rcases GGInnerDiagOnLabel.elim_or
      (S := fun p lab => ggRowP_NF4 p lab ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1) h with h | h
  ·
    exfalso
    obtain ⟨-, hp3⟩ : ∃ _ : True, p = 3 := by
      obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
      exact ⟨trivial, hS.2.1⟩
    subst hp3
    have hF4 : GGF4ThreeMarking Bs X := by
      refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
      obtain ⟨⟨htag, -⟩, -, hdvd⟩ := hP.1
      exact ⟨⟨htag, rfl, hdvd⟩, hP.2.1, hP.2.2⟩
    exact ggRow_absurd_F4Three_of_KG1 (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hcfg hpres h3 hXA hF4
  · exact absurd h hrest

theorem GGGenResidualFrameInputOf.apply
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hU62 : GGU62OuterDiagInput) (hFix : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hRk : GGTwE6ThreeNbrRankInput) (hWI : GGNbrInnerWeylInput) (hLB : GGLBalanceInput)
    (hTCJ : GGTCJKnown) (h : GGGenResidualFrameInputOf T)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hA : ¬ GGIsWeylMatrixA M) {X : Subgroup G}
    (hX : X = L ∨ (X ∈ 𝒦 ∧ ¬ NSJoin.NSTypeD M) ∨ (T M ∧ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X))
    (hnsX : ¬ GGSplitLie p X) (hXU : ¬ GGMemberUnitary p Bs X)
    (hQ4X : X ≠ L → ¬ NSJoin.NSTypeD M → p = 3 → GGInnerDiagOnLabel GGLabQFour p Bs X) :
    GGResidualGenFrame p Bs X ∨ GGGenConcl M Bs X L 𝒦 e := by
  by_cases hBaseTwo : X = L ∧
      GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X
  · obtain ⟨rfl, hmark⟩ := hBaseTwo
    exact Or.inr (ggGenConcl_of_e7Two_base_marking hcfg hpres h3 hbig hmark)
  by_cases hXL : NSJoin.NSTypeD M ∧ X = L
  ·
    obtain ⟨hD, rfl⟩ := hXL
    exact Or.inl (Or.inl (NSJoin.exists_orthWeakFrame_L_typeD_of_guard hFix hU62 hcfg hpres hD hns hXU hbig))
  by_cases hR : ¬ NSJoin.NSTypeD M → GGInnerDiagOnLabel ggRowP_ResGenExcFrame p Bs X
  · exact h G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig hA X hX hnsX hXU hR fun hD hXL' => hXL ⟨hD, hXL'⟩
  · obtain ⟨hD, -⟩ := not_imp.mp hR
    have hE : GGIsWeylMatrixE M := GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 h3 hA hD
    have hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X := by
      rcases hX with hXL | ⟨hXK, -⟩ | ⟨-, hw⟩
      · exact Or.inl hXL
      · exact Or.inr (GGSecFiveWeakNbr.of_mem hcfg hXK)
      · exact Or.inr hw
    have hXn : X = L ∨ ∃ y, GGNbr p B x D J y X := hXw.imp_right fun hw => hw.1
    by_cases hE7 : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) p Bs X
    · refine Or.inl (Or.inr (Or.inr (Or.inl ?_)))
      by_cases hp3 : p = 3
      · subst hp3
        exact ExcPay.exists_excPhanPayload_of_route_E7_three hcfg hXn hE7
      · exact ExcPay.exists_excPhanPayload_of_marking_E7 (ggRouteCfg_prime hcfg).1 hp3
          hcfg.1.1.2.1.2.1 hcfg.1.1.2.1.2.2.2 hE7
    by_cases hTwP : p ≠ 3 ∧ GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X
    · exact Or.inl (Or.inr (Or.inl (ExcPay.exists_excPhanPayload_of_marking_TwE6 (ggRouteCfg_prime hcfg).1
        hTwP.1 hcfg.1.1.2.1.2.1 hcfg.1.1.2.1.2.2.2 hTwP.2)))
    have hTwo : ¬ GGInnerDiagOnLabel ggRowP_ResGenRestTwo p Bs X := by
      intro hTw
      by_cases hXL' : X = L
      · subst hXL'
        exact NSJoin.not_innerDiagOnLabel_resGenRestTwo_L_typeE hFix hU62 hcfg hpres hE hbig hTw
      · exact NSJoin.not_innerDiagOnLabel_qFour_of_resGenRestTwo ggLabelRigidInput_holds hTw
          (hQ4X hXL' hD (NSJoin.eq_three_of_innerDiagOnLabel_resGenRestTwo (ggRouteCfg_prime hcfg).1 hTw))
    by_cases hTw3 : p = 3 ∧ GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X
    · exact Or.inr (ggGenConcl_of_twE6Three_resGen hRk hcfg hpres h3 hXw hTw3.1 hTw3.2)
    have hExc : ¬ GGInnerDiagOnLabel ggRowP_ResGenExc p Bs X := by
      intro hR'
      have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
        rcases hXw with rfl | hw
        · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
        · exact hw.2
      have hsplit : GGInnerDiagOnLabel (fun p lab => ggRowP_EE8 p lab ∨
          (ggRowP_ETwE6 p lab ∧ lab.n = 1) ∨ (ggRowP_EE7 p lab ∧ lab.n = 1) ∨
          (ggRowP_EE7 p lab ∧ 2 ≤ lab.n) ∨ (ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n)) p Bs X := by
        refine hR'.mono_label_of_hasLabel fun lab hΛ _ h => ?_
        have hn1 : 1 ≤ lab.n := hΛ.1
        rcases h with hTw | hE7' | hE8
        · by_cases hn : lab.n = 1
          · exact Or.inr (Or.inl ⟨hTw, hn⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hTw, by omega⟩)))
        · by_cases hn : lab.n = 1
          · exact Or.inr (Or.inr (Or.inl ⟨hE7', hn⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hE7', by omega⟩)))
        · exact Or.inl hE8
      rcases GGInnerDiagOnLabel.elim_or hsplit with h8 | h6F
      · exact ggRow_absurd_EE8 ggLabelRigidInput_holds hFix hWA hcfg e hE hXn hXA
          h8
      rcases GGInnerDiagOnLabel.elim_or h6F with h6 | hF
      · exact ggRow_absurd_TwE6Two ggLabelRigidInput_holds hFix hWI hLB hTCJ hcfg hns hpres h3 hbig hA hD
          (fun hXL' hp3 => hQ4X hXL' hD hp3) h6
      · rcases GGInnerDiagOnLabel.elim_or hF with h7 | hF
        · have hXL' : X ≠ L := fun hXL' => hBaseTwo ⟨hXL', h7⟩
          have hp3 : p = 3 := NSJoin.eq_three_of_innerDiagOnLabel_n_one (ggRouteCfg_prime hcfg).1
            (fun _ h => ⟨h.2, h.1.2⟩) h7
          exact NSJoin.not_innerDiagOnLabel_qFour_of_n_one ggLabelRigidInput_holds
            (fun _ h => ⟨h.2, by simp [h.1.1], by simp [h.1.1]⟩) h7 (hQ4X hXL' hD hp3)
        · rcases GGInnerDiagOnLabel.elim_or hF with h7q | h6q
          · exact hE7 h7q
          · by_cases hp3 : p = 3
            · exact hTw3 ⟨hp3, h6q⟩
            · exact hTwP ⟨hp3, h6q⟩
    refine Or.inl (Or.inl (ggResGenFrame_of_not_rest hcfg hpres h3 hXw hnsX hXU fun h' => ?_))
    rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ResGenExc) (T := ggRowP_ResGenRestTwo)
        (h'.mono' fun lab hl => ggRowP_ResGenRest_iff.mp hl) with h' | h'
    · exact hExc h'
    · exact hTwo h'

theorem GGGenResidualFrameInputOf.baseRefl
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hD : PhanDInput2) (hPE : PhanEInput2)
    (hRk : GGTwE6ThreeNbrRankInput) (hU62 : GGU62OuterDiagInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hWI : GGNbrInnerWeylInput) (hTCJ : GGTCJKnown)
    (h : GGGenResidualFrameInputOf T) : GGSecFiveBaseReflInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig
  by_cases hU : GGMemberUnitary p Bs L
  · exact ggMemberUnitary_baseRefl hcfg hpres h3 hU
  ·
    have hA : ¬ GGIsWeylMatrixA M := fun ⟨_, _, _, hM⟩ =>
      hU (ggMemberUnitary_anyA hRk hU62 hFix hWA hLB hSP hcfg hns hpres hM hbig (Or.inl rfl) hns)
    have hgen : GGGenConcl M Bs L L 𝒦 e := by
      rcases h.apply hU62 hFix hWA hRk hWI hLB hTCJ hcfg hns hpres h3 hbig hA (X := L) (Or.inl rfl) hns hU
          (fun hLL => absurd rfl hLL) with hF | hC
      · have hp := ggRouteCfg_prime hcfg
        haveI : Fact p.Prime := ⟨hp.1⟩
        exact ggGenConcl_of_le_iSup_isReflection hcfg hpres h3 (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
          (hF.le_iSup_rankOne hD hPE hp.2)
      · exact hC
    by_contra hne
    have hne : ∀ r ∈ ggAutomizer L Bs, r ∉ ggCoxRefl M e := fun r hr hr' => hne ⟨r, hr, hr'⟩
    refine ggRouteCfg_ne_bot hcfg (le_bot_iff.mp ?_)
    calc L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
          ggRankOneIn L Bs r := hgen
      _ ≤ ⊥ := iSup₂_le fun r hr => absurd hr.2 (hne r hr.1)

theorem GGGenResidualFrameInputOf.toWeak
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hD : PhanDInput2) (hPE : PhanEInput2) (hL1 : GGSecFiveL1PhanInput)
    (hRk1 : GGSecFiveRk1PhanInput) (hRk : GGTwE6ThreeNbrRankInput) (hU62 : GGU62OuterDiagInput) (hFix : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hPos : NSJoin.NSWeakOrthPosInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSJoin.NSTypeD M))
    (hNbrQ4 : NSJoin.NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => GGIsWeylMatrixE M))
    (hWI : GGNbrInnerWeylInput) (hTCJ : GGTCJKnown)
    (h : GGGenResidualFrameInputOf T) : GGGenResidualWeakInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig X hX hnsX _
  have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hX with hXL | hXK | ⟨-, hw⟩
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl hXL)
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inr hXK)
    · exact hw.2
  by_cases hXU : GGMemberUnitary p Bs X
  ·
    have hXnbr : X = L ∨ ∃ y : G, GGNbr p B x D J y X := by
      rcases hX with hXL | hXK | ⟨-, hw⟩
      · exact Or.inl hXL
      · exact Or.inr (hcfg.2.2.2.1.2 X hXK)
      · exact Or.inr hw.1
    obtain ⟨r₀, hrLA, hr₀C⟩ :=
      h.baseRefl hD hPE hRk hU62 hFix hWA hLB hSP hWI hTCJ G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig
    have hRkL : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs L r :=
      fun r hrA hrC => hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 L (Or.inl rfl) r hrA hrC
    have hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
      hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig L (Or.inl rfl) r₀ hrLA hr₀C
    exact ggGenConcl_unitary_nbr hcfg hns hpres h3 hbig hXnbr hXA hnsX hXU ⟨r₀, hrLA, hr₀C⟩
      (fun r hrA hrC => ggL1_transfer_nbr hcfg hns hpres h3 hrLA hr₀C (hbig r₀ hrLA hr₀C) hseed hXnbr hrA hrC
        (hRkL r₀ hrLA hr₀C) (ggRk1Concl_unitary_nbr hcfg hpres hXnbr hnsX hXU hrA hrC))
      (fun r hrA hrC => hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig L (Or.inl rfl) r hrA hrC)
  ·
    have hA : ¬ GGIsWeylMatrixA M := by
      rintro ⟨_, _, _, hM⟩
      refine hXU (ggMemberUnitary_anyA hRk hU62 hFix hWA hLB hSP hcfg hns hpres hM hbig ?_ hnsX)
      rcases hX with hXL | hXK | ⟨-, hw⟩
      · exact Or.inl hXL
      · exact Or.inr ⟨hcfg.2.2.2.1.2 X hXK, hXA⟩
      · exact Or.inr hw
    have hF : GGResidualGenFrame p Bs X ∨ GGGenConcl M Bs X L 𝒦 e := by
      by_cases hXD : X ∈ 𝒦 ∧ NSJoin.NSTypeD M
      · exact Or.inl (Or.inl (hPos G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hXD.2, hbig⟩ X
          (GGSecFiveWeakNbr.of_mem hcfg hXD.1) hnsX hXU))
      · refine h.apply hU62 hFix hWA hRk hWI hLB hTCJ hcfg hns hpres h3 hbig hA (X := X) ?_ hnsX hXU ?_
        · rcases hX with hXL | hXK | hTw
          · exact Or.inl hXL
          · exact Or.inr (Or.inl ⟨hXK, fun hDM => hXD ⟨hXK, hDM⟩⟩)
          · exact Or.inr (Or.inr hTw)
        ·
          intro hXL hDM hp3
          subst hp3
          obtain ⟨y, hnb⟩ : ∃ y : G, GGNbr 3 B x D J y X := by
            rcases hX with hXL' | hXK | ⟨-, hw⟩
            · exact absurd hXL' hXL
            · exact hcfg.2.2.2.1.2 X hXK
            · exact hw.1
          exact hNbrQ4 G B Bs x L D J 𝒦
            ⟨hcfg, hns, ι, M, e, hpres, GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 h3 hA hDM, hbig⟩ y X hnb
    rcases hF with hF | hC
    · have hp := ggRouteCfg_prime hcfg
      haveI : Fact p.Prime := ⟨hp.1⟩
      exact ggGenConcl_of_le_iSup_isReflection hcfg hpres h3 hXA (hF.le_iSup_rankOne hD hPE hp.2)
    · exact hC

end Proofs

end CFSG.StandardType

end
