module
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsN
public import CFSG.LocalAnalysis.StandardType.GGOriginalTwE6TwoNoncommRoute
import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylInputHolds
import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
import CFSG.LocalAnalysis.StandardType.GGPairResidualUnitaryTwo
import CFSG.LocalAnalysis.StandardType.GGPairResidualE7Plus
import CFSG.LocalAnalysis.StandardType.GGPairResidualE8Plus
import CFSG.LocalAnalysis.StandardType.GGPairResidualTwE6Plus
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseEnnolaTwo
import CFSG.LocalAnalysis.StandardType.GGPairResidualOrthTwo
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPair
public noncomputable section
namespace CFSG.StandardType
open CFSG.Assembly CFSG.Open CFSG.ClassicalInvolution.Phan

theorem ggPairResidualMemberInput_of_row_inputs
    (hTw3 : ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)),
      GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 → ¬ GGSplitLie 3 L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
      GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e →
      (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
      ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie 3 X →
      ¬ GGMemberUnitary 3 Bs X → GGInnerDiagOnLabel ggRowP_ETwE6 3 Bs X →
      ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
      ∀ s ∈ ggAutomizer X Bs, s ∈ ggCoxRefl M e → r ≠ s → GGPairConcl Bs X r s) :
    GGPairResidualMemberInput := by
  classical
  have hP : GGStdSubPrimeInput := ggStdSubPrimeInput_holds
  have hWA : GGTBFixNbrXInput := ggTBFixNbrXInput_holds
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hXs hXu
    r hrA hrC s hsA hsC hne
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hRows : GGInnerDiagOnLabel ggRowP_E p Bs X :=
    ggX_eRow_of_nonSplit hcfg hpres hle3
      (hX.imp_right (GGSecFiveWeakNbr.of_mem hcfg)) hXs
  have hRows' : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∨ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∨
        ggRowP_ETwE6 p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab) p Bs X :=
    GGInnerDiagOnLabel.mono' (fun lab hrow => by
      rcases hrow with hSU | hOp | hOm | hTw | hE7 | hE8
      · exact Or.inl hSU
      · exact Or.inr (Or.inl (Or.inl hOp))
      · exact Or.inr (Or.inl (Or.inr hOm))
      · exact Or.inr (Or.inr (Or.inl hTw))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hE7)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hE8)))) hRows
  rcases hRows'.elim_or with hSU | hRows'
  · have hCases : GGInnerDiagOnLabel
        (fun p lab => (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
          (ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) p Bs X :=
      GGInnerDiagOnLabel.mono' (fun lab hrow => by
        by_cases hex : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)
        · exact Or.inr ⟨hrow, hex⟩
        · exact Or.inl ⟨hrow, hex⟩) hSU
    rcases hCases.elim_or with hOrd | hExceptional
    · exact (hXu hOrd).elim
    · exact ggPairConcl_of_selected_unitary_two_exceptional ggTBFixInput_holds hP hWA
        G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hXs hXu hExceptional
        r hrA hrC s hsA hsC hne
  rcases hRows'.elim_or with hOm | hRows'
  · have hCases : GGInnerDiagOnLabel
        (fun p lab => (lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) ∨
          ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n)) p Bs X :=
      GGInnerDiagOnLabel.mono' (fun lab hrow => by
        have hdvd : p ∣ 2 ^ lab.n + 1 := by
          rcases hrow with hOp | hOm
          · exact hOp.2.2.2
          · exact hOm.2.2.2
        have hnpos : 1 ≤ lab.n := by
          by_contra hn
          have hn0 : lab.n = 0 := by omega
          have hpdiv : p ∣ 2 := by simpa [hn0] using hdvd
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv)
        by_cases hn1 : lab.n = 1
        · exact Or.inl ⟨hn1, hrow⟩
        · exact Or.inr ⟨hrow, by omega⟩) hOm
    rcases hCases.elim_or with hTwo | hGeFour
    · exact ggPairConcl_of_orthogonal_two G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3
        X hX hTwo r hrA hrC s hsA hsC hne
    · exact ggPairConcl_of_orthogonal_ge_four G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3
        X hX hXs hXu hGeFour r hrA hrC s hsA hsC hne
  rcases hRows'.elim_or with hTw | hRows'
  · by_cases hp3 : p = 3
    · subst p
      exact hTw3 G B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hXs hXu hTw
        r hrA hrC s hsA hsC hne
    · exact ggPairConcl_of_selected_TwE6_plus_of_ne_three hp3 hcfg hns hpres hle3
        hX hXs hXu hTw hrA hrC hsA hsC hne
  rcases hRows'.elim_or with hE7 | hE8
  · exact ggPairConcl_of_selected_E7_plus hcfg hns hpres hle3 hX hXs hXu hE7
      hrA hrC hsA hsC hne
  · exact ggPairConcl_of_selected_E8_plus hcfg hns hpres hle3 hX hXs hXu hE8
      hrA hrC hsA hsC hne


theorem ggPairResidualMemberInput_holds : GGPairResidualMemberInput := by
  apply ggPairResidualMemberInput_of_row_inputs
  intro G _ _ B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX hXs hXu hTw
    r hrA hrC s hsA hsC hne
  have hCases : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_ETwE6 p lab ∧ lab.n = 1) ∨
        (ggRowP_ETwE6 p lab ∧ 3 ≤ lab.n)) 3 Bs X :=
    hTw.mono' fun lab hrow => by
      by_cases hn3 : 3 ≤ lab.n
      · exact Or.inr ⟨hrow, hn3⟩
      · rcases (by omega : lab.n = 0 ∨ lab.n = 1 ∨ lab.n = 2) with hn | hn | hn
        · have hdvd := hrow.2
          norm_num [hn] at hdvd
        · exact Or.inl ⟨hrow, hn⟩
        · have hdvd := hrow.2
          norm_num [hn] at hdvd
  rcases hCases.elim_or with hTwo | hLarge
  · exact ggTwE6Two_original_pair_of_route_proved hcfg hns hpres h3 hX hXs hXu hTwo
      hrA hrC hsA hsC hne
  · exact CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.ggPairConcl_of_large_twE6_member_of_route_proved
      hcfg hX hLarge hpres hrA hrC hsA hsC hne

theorem ggSecFivePhanPairNInput_of_full_residual_pairs : GGSecFivePhanPairNInput :=
  ggSecFivePhanPairNInput_of_rows ggPairUnitaryMemberInput_holds
    (ggPairResidualMemberNInput_of_rest
      (ggPairResidualMemberRestInput_of_residual ggPairResidualMemberInput_holds))

end CFSG.StandardType
