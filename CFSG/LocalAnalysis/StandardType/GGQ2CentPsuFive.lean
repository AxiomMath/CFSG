module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentPsuFiveCore
public import CFSG.LocalAnalysis.StandardType.GGQ2CentPsuFiveModel
public import CFSG.LocalAnalysis.StandardType.GGQ2CentPsuSixModel
public import CFSG.LocalAnalysis.StandardType.GGQ2CentTransport

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

theorem psuAtLeastFiveTwoInput_of_six
    (h6 : labelTUInput fun lab => lab.tag = .twA ∧ lab.rank = 5) :
    psuAtLeastFiveTwoInput := by
  refine labelTUInput_of_exists _ fun G _ _ p B Bs x L D J hS hon => ?_
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hperf, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, htag, hrk⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  obtain ⟨K, _, _, hK, θ', hBs3⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ 1) ^ 2 ∧
      ∃ θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K (lab.rank + 1)),
        ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (unitarySU 2 1 K (lab.rank + 1)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ 1)),
          LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    obtain ⟨t, r, n⟩ := lab
    dsimp only at hn htag ⊢
    subst hn htag
    obtain ⟨K, i1, i2, hK, -, -, θ', -, -, hBs3⟩ := hraw
    exact ⟨K, i1, i2, hK, θ', hBs3⟩
  refine ⟨_, _, θ', fun hN => ?_⟩
  by_cases h5 : lab.rank = 5
  · refine h6 G 3 B Bs x L D J hS ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩ _ θ' hN
    rintro R _ I F ⟨hs, hna, θ'', ⟨hq2', htag', -⟩, hrest⟩
    exact ⟨hs, hna, θ'', ⟨hq2', htag', h5⟩, hrest⟩
  · obtain ⟨ψ, hψ, hdiag⟩ := exists_diagModel_twA hS hN hK (by omega) (by omega) θ' hBs3
    have h := toralAt_internalAt_of_diagModel hS θ' hN (by omega) hψ hdiag
    exact ⟨h.1, fun _ => h.2⟩

theorem psuSixTwoInput_holds :
    labelTUInput fun lab => lab.tag = .twA ∧ lab.rank = 5 := by
  refine labelTUInput_of_exists _ fun G _ _ p B Bs x L D J hS hon => ?_
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨-, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, htag, hrk⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  obtain ⟨K, _, _, hK, θ', hBs3⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ 1) ^ 2 ∧
      ∃ θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6),
        ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
          (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
          LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    obtain ⟨t, r, n⟩ := lab
    dsimp only at hn htag hrk ⊢
    subst hn htag hrk
    obtain ⟨K, i1, i2, hK, -, -, θ', -, -, hBs3⟩ := hraw
    exact ⟨K, i1, i2, hK, θ', hBs3⟩
  refine ⟨_, _, θ', fun hN => ?_⟩
  have hL : commutator L = ⊤ := (isQuasisimple_of_largeEvenMarking (K := L) hS.2.1).1
  obtain ⟨ψ, hψ, hdiag⟩ := exists_quotModel_six hS.1.1 hL hN hK θ' hBs3
  have hZ3 : ¬ 3 ∣ Nat.card (U63TB.twoSub (Subgroup.center L) le_rfl) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (U63TB.isPGroup_twoSub (N := Subgroup.center L) le_rfl).exists_card_eq
    rw [hk]
    intro h
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h32
  have h := toralAt_internalAt_of_quotModel hS θ' hN _ (U63TB.twoSub_le_center (N := Subgroup.center L) le_rfl) hZ3
    (by norm_num) hψ hdiag
  exact ⟨h.1, fun _ => h.2⟩

theorem psuAtLeastFiveTwoInput_holds :
    psuAtLeastFiveTwoInput :=
  psuAtLeastFiveTwoInput_of_six psuSixTwoInput_holds

end CFSG.StandardType.GGQ2CentPort

end
