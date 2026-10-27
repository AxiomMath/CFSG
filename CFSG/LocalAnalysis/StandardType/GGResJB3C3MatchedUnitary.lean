module

public import CFSG.LocalAnalysis.StandardType.GGResJA2UnitaryRecognition
import CFSG.LocalAnalysis.StandardType.GGA2UnitaryIThreeRank
import CFSG.LocalAnalysis.StandardType.GGResJLineBCGamma

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGResHyp.actual_J_not_matched_unitary_for_B3C3
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G} {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J T) (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≠ 5) 3 Bs J) :
    False := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, r, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hP0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hS, _, _⟩ := hP0
  have htag : tag = .twA := hS.1
  have hpq : 3 ∣ 2 ^ n + 1 := hS.2.1
  have hr5 : r ≠ 5 := hS.2.2
  subst htag
  have hΛ' := hΛ
  dsimp only [LargeEvenInLambda2] at hΛ'
  obtain ⟨hn, hr2le, hr2n⟩ := hΛ'
  rcases Nat.lt_or_ge r 3 with hrlt | hrge
  ·
    have hr2 : r = 2 := by omega
    subst r
    have h2n : 2 ≤ n := hr2n rfl
    have hA2 : GGLabelA2 ⟨.twA, 2, n⟩ := ⟨rfl, h2n, Or.inr ⟨rfl, hpq⟩⟩
    have hall : LargeEvenLabelAll ⟨.twA, 2, n⟩ (GGRawIThreeRankLe 9) :=
      ggA2UnitaryIThreeRank_holds ⟨.twA, 2, n⟩ hΛ hA2 rfl
    obtain ⟨R, _, I, F, ⟨hQR, hlt⟩⟩ := largeEvenRawDatum_exists (hall _ hraw)
    obtain ⟨_, _, θ, hP⟩ := hQR
    have hNmark : Bs ≤ Subgroup.normalizer (J : Set G) := hP.2.1
    have hind := hP.2.2
    let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
    have hgamma : ggGamma J hNmark = ggGamma J hN0 := by ext b; rfl
    let A : Subgroup (MulAut ↥J) := (ggGamma J hNmark).range
    have hAe : CFSG.Open.IsElemAbelian 3 A := by
      dsimp [A]
      exact isElemAbelian_range
        (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
        (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
        (ggGamma J hNmark)
    let B' : Subgroup (MulAut R) := A.map (ggInducedAut θ)
    have hBcard : Nat.card B' = Nat.card A :=
      Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hperfJ θ)
    have hBe : CFSG.Open.IsElemAbelian 3 B' := hAe.map _
    have hBI : (B' : Set (MulAut R)) ⊆ I := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, rfl⟩ := ha
      have hmem := ggBeta_mem J θ hNmark hind b
      have hbeta : ggBeta J θ hNmark b = ggInducedAut θ (ggGamma J hNmark b) := by
        rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
        rfl
      rwa [hbeta] at hmem
    have hle9 : Nat.card A ≤ 9 := by
      rw [← hBcard]
      exact hlt B' hBe hBI
    have h27 : 3 ^ 3 ≤ Nat.card A := by
      simpa only [A, hgamma] using cube_le_card_gamma_of_B3C3 hN0 hD hT
    norm_num at h27
    omega
  ·
    have hr3 : 3 ≤ r := hrge
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
    let _ : Field F := hFfield
    let _ : Finite F := hFfinite
    obtain ⟨_, _, θ, hP⟩ := hQ
    obtain ⟨_, hN, hBsI⟩ := hP
    let d : ℕ := r + 1
    have hd3 : 3 ≤ d := by dsimp [d]; omega
    let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))
    let I : Set (MulAut R) :=
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
        (LargeEvenGUSet (Fin d) F (2 ^ n))
    let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
    have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
    let A : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
    have hψ : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
    have hker : (ggQuotHom θ).ker ≤ Subgroup.center ↥J := by
      rw [ker_ggQuotHom θ]
    have hAe : IsElemAbelian 3 A := by
      dsimp [A]
      exact isElemAbelian_range
        (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
        (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
        (ggGamma J hN0)
    have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J,
        φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
      rintro a ⟨b, rfl⟩
      exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBsI b, fun l => by
        rw [ggBeta_ggQuotHom J hN θ b l, hgamma]⟩
    have hsc : GGTorusSelfCent 3 A := by
      simpa [A, hgamma] using GGResHyp.gamma_J_selfCent hH
    have hcardBC : Nat.card (ggAutomizer J Bs) = 48 := by
      rcases hT with rfl | rfl
      · exact ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
      · exact ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
    have hfacNe : Nat.card (ggAutomizer J Bs) ≠ 48 := by
      by_cases hr3eq : r = 3
      · subst r
        have hodd : Odd (2 ^ n + 1) := by
          have hnpos : 0 < n := by omega
          exact (Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hnpos⟩).add_one
        have hcop : Nat.Coprime 4 (2 ^ n + 1) := by
          rw [show 4 = 2 ^ 2 by norm_num]
          exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 (2 ^ n + 1)).2
            (Nat.coprime_two_left.mpr hodd)
        have hTor := ggTorusTorW_unitary_liftTwo_weak
          (K := F) (n := n) (p := 3) (N := 3)
          hFcard hn (by norm_num) (by norm_num) hpq hcop
          hψ hker hperfJ hAe hAI hsc
        have h24 := card_ggAutomizer_eq_factorial_of_unitaryTorusData
          (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0) hpq hTor
        rw [show Nat.factorial 4 = 24 by norm_num] at h24
        omega
      · have hr4 : 4 ≤ r := by omega
        by_cases hpd : 3 ∣ r + 1
        · have hr8 : 8 ≤ r := by
            obtain ⟨k, hk⟩ := hpd
            have hk2 : 2 ≤ k := by omega
            have hkne : k ≠ 2 := by
              intro hk2eq
              exact hr5 (by omega)
            have hk3 : 3 ≤ k := by omega
            omega
          have hdq : (d, 2 ^ n) ≠ (3, 2) := by
            intro heq
            have := congrArg Prod.fst heq
            dsimp [d] at this
            omega
          have hLift : GGTorusLift 3 (r - 2) R := by
            have h := ggTorusLift_unitary (K := F) (n := n) (d := d) (p := 3)
              hFcard hn hd3 hdq (by norm_num) hpq
            simpa [R, d, ggUnitaryTorusRank, hpd] using h
          have hpow : 3 ^ (r - 2) ≤ Nat.card A := by
            simpa [A, hgamma] using
              GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift
          have hTB : GGTorusTBGroup 3 (r - 2) R I ↥J (ggQuotHom θ) A := by
            refine ⟨hψ, hker, hperfJ, hAe, hAI, hpow, ?_, hsc⟩
            exact (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ r - 2)).trans hpow
          have hTorW := ggTorusTorW_unitary LineU.unitaryUniversalCover_holds
            (K := F) (n := n) (p := 3) (N := r)
            hFcard (by omega) hr4 (by norm_num) hpq hpd (by
              rintro ⟨h6, -⟩
              exact hr5 (by omega))
          have hTor := hTorW ↥J (ggQuotHom θ) A hTB
          have hfac := card_ggAutomizer_eq_factorial_of_unitaryTorusData
            (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0) hpq hTor
          have hge : 120 ≤ (r + 1).factorial := by
            rw [show (120 : ℕ) = Nat.factorial 5 by norm_num]
            exact Nat.factorial_le (by omega)
          omega
        · have hU : LineU.UnitaryCoverAt n (r + 1) F :=
            LineU.unitaryUniversalCover_holds n (r + 1) F hFcard (by omega) (by
              intro h6
              have h6' : r + 1 = 6 := congrArg Prod.fst h6
              exact hpd (by rw [h6']; norm_num))
          have hTor := ggTorusTorW_unitary_coprime_weak
            (K := F) (n := n) (p := 3) (N := r)
            hFcard hn (by omega) (by norm_num) hpq hpd hU
            hψ hker hperfJ hAe hAI hsc
          have hfac := card_ggAutomizer_eq_factorial_of_unitaryTorusData
            (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0) hpq hTor
          have hge : 120 ≤ (r + 1).factorial := by
            rw [show (120 : ℕ) = Nat.factorial 5 by norm_num]
            exact Nat.factorial_le (by omega)
          omega
    exact hfacNe hcardBC

end CFSG.StandardType

end
