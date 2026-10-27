module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBTwA3Row
public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTPNPCompDefs
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeSixHeart
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGTPNAtL
import CFSG.LocalAnalysis.StandardType.GGTPNLineFinal
import CFSG.LocalAnalysis.StandardType.GGB36StepOneK0
import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
import CFSG.LocalAnalysis.StandardType.GGKacExcB2
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo
import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3Rows
import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggLabelIso_twA3_cases {m : ℕ} {lab : LargeEvenLabel}
    (h : GGLabelIso ⟨.twA, 3, m⟩ lab) : lab = ⟨.twA, 3, m⟩ ∨ lab = ⟨.twD, 3, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h.symm
  · rcases h with h | h <;> cases h
  · cases h
  · cases h
  · cases h
  · exact Or.inr h
  · cases h
  · cases h

theorem ggQ2TablePAtLTwA3_of_known (hRig : GGLabelRigidInput)
    (hKn : GGTablePKnownRK GGRegimeLine) (h1 : GGB36StepOne)
    (hQ : GGPCompCentQuasisimple fun _ => True) (hP : GGStdSubPrimeInput) :
    GGQ2TablePAtLTwA3 := by
  intro G _ _ B Bs x L D J hS hI1 hcard y K hn labJ hΛJ htJ hrJ hpq hhJ
  obtain ⟨t, r, m⟩ := labJ
  simp only at htJ hrJ
  subst htJ hrJ
  have hc : GGConfig 3 B Bs x L D J := hS.1.1
  have hL2 : GGInnerDiagOnLabel GGLabQTwo 3 Bs L := hS.2.1
  have hInn : GGInnerDiagOn Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hL2
  have hpJ : 3 ∣ Nat.card J := hP G 3 B x L D J hc.1 hc.2.2
  have hI1' : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := fun b hb =>
    hI1 b hb.1 fun j hj => (Subgroup.mem_centralizer_iff.mp hb.2 j hj).symm
  have hTJ : ggResLineJLabel .A3 ⟨.twA, 3, m⟩ := Or.inr ⟨Or.inl rfl, rfl, hpq⟩
  obtain ⟨labJ', labL', hΛJ', hΛL', hrow, hhJ', hhL'⟩ :=
    ggTPNRow_atL_line hRig hKn hQ hc hL2 hpJ hn.2.1 hI1' hcard hΛJ hTJ hhJ
  have hisoJ := hRig _ labJ' _ hΛJ hΛJ' hhJ hhJ'
  have hJ' := ggLabelIso_twA3_cases hisoJ
  obtain ⟨labL, hΛL, hhL, -, -, -, -, -, hqL, -⟩ := largeEvenMarking_exists_hasLabel hL2
  have hnL : labL.n = 1 := by
    have h1' : 1 ≤ labL.n := hΛL.1
    have h2' : labL.n < 2 := hqL
    omega
  have hL'n : labL'.tag ≠ .A → labL'.n = 1 := fun hA => by
    rcases FrameRoute.ggFrameQTwo_qTwoCompat_of_iso hnL (hRig labL labL' _ hΛL hΛL' hhL hhL')
      with h | ⟨h, -⟩
    · exact h
    · exact absurd h hA
  rcases ggTablePRow_three_A3 (ggResLineJLabel_of_iso hTJ hisoJ) hrow with
    ⟨htA, -⟩ | ⟨htD, -⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · exfalso
    rcases hJ' with h | h <;> rw [h] at htA <;> cases htA
  · exfalso
    rcases hJ' with h | h <;> rw [h] at htD <;> cases htD
  · rcases hX with h | h | h | h | h | ⟨htw, -⟩
    · have hn1 : labJ'.n = 1 := by
        have h' := hL'n (by rw [h]; simp)
        rwa [h] at h'
      exact ⟨labL', by rw [h, hn1]; exact Or.inl rfl, hhL'⟩
    · have hn1 : labJ'.n = 1 := by
        have h' := hL'n (by rw [h]; simp)
        rwa [h] at h'
      exact ⟨labL', by rw [h, hn1]; exact Or.inr (Or.inl rfl), hhL'⟩
    · have hn1 : labJ'.n = 1 := by
        have h' := hL'n (by rw [h]; simp)
        rwa [h] at h'
      exact ⟨labL', by rw [h, hn1]; exact Or.inr (Or.inr (Or.inl rfl)), hhL'⟩
    · have hn1 : labJ'.n = 1 := by
        have h' := hL'n (by rw [h]; simp)
        rwa [h] at h'
      exact ⟨labL', by rw [h, hn1]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))), hhL'⟩
    · have hn1 : labJ'.n = 1 := by
        have h' := hL'n (by rw [h]; simp)
        rwa [h] at h'
      exact ⟨labL', by rw [h, hn1]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl))), hhL'⟩
    ·
      exfalso
      obtain ⟨labJ'', hB36, hΛJ'', hhJ''⟩ :=
        h1 G 3 B Bs x L D J hc hInn rfl labL' hΛL' (Or.inr htw) hhL'
      rcases ggLabelIso_twA3_cases (hRig _ labJ'' _ hΛJ hΛJ'' hhJ hhJ'') with h | h <;>
      · rw [h] at hB36
        simp [GGB36JLabel, htw] at hB36
  · have hn1 : labJ'.n = 1 := by
      have h' := hL'n (by rw [hX]; simp)
      rwa [hX] at h'
    exact ⟨labL', by rw [hX, hn1]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))), hhL'⟩

theorem ggQ2TablePAtLTwA3_holds
    (hB3 : GGK0ExcB3) (hQ : GGPCompCentQuasisimple fun _ => True) (hP : GGStdSubPrimeInput) :
    GGQ2TablePAtLTwA3 :=
  ggQ2TablePAtLTwA3_of_known ggLabelRigidInput_holds (ggTablePKnownRK_line_of_B3 hB3)
    (ggB36StepOne_of_K0REMult (ggK0CompREMult_of_excB (GGK0ExcB2.toExcB (GGK0ExcB3.toB2 hB3))))
    hQ hP

theorem ggQ2s08_tn6_of_leaves
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput)
    (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput) (hT : GGTPNTransferBNoCorners)
    (hB3 : GGK0ExcB3) (hQ : GGPCompCentQuasisimple fun _ => True) :
    GGQ2S08TNCell (GGQ2S08PosTwA 6) :=
  ggQ2s08_tn6_holds ggLabelRigidInput_holds hLB hP hNC h5 hK ggQ2_cavOfTBHeartInner_holds
    (ggNbrTablePNbrInputI1On_line_of_leaves hT hB3) (ggQ2TablePAtLTwA3_holds hB3 hQ hP)

end CFSG.StandardType

end
