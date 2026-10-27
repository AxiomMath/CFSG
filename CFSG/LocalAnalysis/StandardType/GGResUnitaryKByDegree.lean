module

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryRankNineK3
public import CFSG.LocalAnalysis.StandardType.GGResKHighDegree
import CFSG.LocalAnalysis.StandardType.GGResF4BigUnitaryK
import CFSG.LocalAnalysis.StandardType.GGResUnitaryRankEightK3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Cert


theorem ggResMultiNodeRestThreeKUnitaryQGeFourJoinInput_of_rest
    (h : GGResMultiNodeRestThreeKUnitaryQGeFourRestInput) :
    GGResMultiNodeRestThreeKUnitaryQGeFourJoinInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hdata
  obtain ⟨hDK, ⟨lab, hlab, hr5, hn2, hmark⟩, hnK, hE6K, hL2, hLn, hLs, hM, hsmL, hKs, hres,
    htwo, hC2, hSU2⟩ := hdata
  have hU : ∀ ℓ, lab.rank = ℓ → GGInnerDiagOnLabel
      (fun p lab' => lab'.tag = .twA ∧ lab'.rank = ℓ ∧ 2 ≤ lab'.n ∧ p ∣ 2 ^ lab'.n + 1)
      p Bs K := by
    intro ℓ hℓ
    refine GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab) ?_ hmark
    intro lab' hlab'
    subst lab'
    exact ⟨hlab.1, hℓ, hn2, hlab.2.2.2⟩
  by_cases h6 : lab.rank = 6
  · exact ggResLeaf_unitary_rank_six_exactThree_K G p B Bs x L D J y K hH hF hS hE
      ⟨hU 6 h6, hDK, hres, htwo, hC2, hSU2⟩
  by_cases h7 : lab.rank = 7
  · exact ggResLeaf_unitary_rank_seven_exactThree_K G p B Bs x L D J y K hH hF hS hE
      ⟨hU 7 h7, hDK, hres, htwo, hC2, hSU2⟩
  by_cases h9 : lab.rank = 9
  · exact ggResLeaf_unitary_rank_nine_exactThree_K G p B Bs x L D J y K hH hF hS hE
      ⟨hU 9 h9, hDK, hres, htwo, hC2, hSU2⟩
  by_cases h10 : 10 ≤ lab.rank
  · have hU10 : GGInnerDiagOnLabel
        (fun p lab' => lab'.tag = .twA ∧ 10 ≤ lab'.rank ∧ 2 ≤ lab'.n ∧ p ∣ 2 ^ lab'.n + 1)
        p Bs K := by
      refine GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab) ?_ hmark
      intro lab' hlab'
      subst lab'
      exact ⟨hlab.1, h10, hn2, hlab.2.2.2⟩
    exact ggResLeaf_unitary_highDegree_exactThree_K_holds G p B Bs x L D J y K hH hF hS hE
      ⟨hU10, hDK, hres, htwo, hC2, hSU2⟩
  by_cases h8 : lab.rank = 8
  · exact ggResLeaf_unitary_rankEight_exactThree_K G p B Bs x L D J y K hH hF hS hE
      ⟨hU 8 h8, hDK, hres, htwo, hC2, hSU2⟩
  have hr5 : lab.rank = 5 := by omega
  by_cases hF4 : GGInnerDiagOnLabel GGF4ThreeLabel p Bs L
  · have hp3 : p = 3 := by
      have hp : p.Prime := Fact.out
      have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
      have hd : p ∣ 2 * 3 := by simpa [hr5] using hlab.2.2.1
      rcases hp.dvd_mul.mp hd with hd' | hd'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd') hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd'
    subst hp3
    have hK3 : GGInnerDiagOnLabel
        (fun p lab' => ggThreeResidualLabelK p lab' ∧ 2 ≤ lab'.n) 3 Bs K := by
      refine GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab) ?_ hmark
      intro lab' hlab'
      subst lab'
      exact ⟨hlab, hn2⟩
    exact (hH.not_exactThree_K_of_f4Three_L_residual_K hF4 hK3 hDK).elim
  exact h G p B Bs x L D J y K hH hF hS hE
    ⟨hDK, ⟨lab, hlab, hr5, hn2, hmark⟩, hnK, hE6K, hL2, hLn, hLs, hM, hsmL, hF4, hKs, hres,
      htwo, hC2, hSU2⟩

end Cert

end CFSG.StandardType

end
