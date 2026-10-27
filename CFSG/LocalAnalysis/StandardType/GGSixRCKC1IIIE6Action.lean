module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE6Components
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLCube
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOmegaMinusTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType


theorem e6_two_compConfig_linear_or_minus_modelID
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E6 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .E6 n 1 ψ p G₀ A B₁ D J L K e) :
    RCKRP.RCKClassicalModelIDAt .PSL K B₁ ∨
      RCKRP.RCKClassicalModelIDAt .POmegaMinus K B₁ := by
  have hp3 := prime_eq_three_of_e6_two_compConfig hcfg
  have hcover := e6_two_compConfig_exists_native_cover hcfg
  subst p
  obtain ⟨hGG, -, hp, -, hA, hBA, hDB, hDcard, hAN, -, hBNJ, -, -, -, -, -, -, -,
    hJcomp, -, -, -, -, -, -, heD, hene, hKcomp, hJK, -⟩ := hcfg
  have hBNK := (RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcover with ⟨hlabel, φ, hφr, hφk⟩ | ⟨hlabel, φ, hφr, hφk⟩ | ⟨hlabel, φ, hφr, hφk⟩
  · refine Or.inl ⟨6, 1, φ, by decide, hφr, hφk, ?_⟩
    intro b hb
    let φSL : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1) →* X := φ
    have hker : φSL.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) := hφk
    have hbN : b ∈ Subgroup.normalizer (φSL.range : Set X) := by
      change b ∈ Subgroup.normalizer (φ.range : Set X)
      rw [hφr]
      exact hBNK hb
    have hF : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 one_ne_zero, pow_one]
    change GGPsiInnerDiag (SpecialLinear.rootDatum 5 (GaloisField 2 1)) φSL b
    exact ggPsiInnerDiag_sl_of_cube_of_card_eq_two_or_four (by decide) (Or.inl hF)
      hker hbN (hA.2 b (hBA hb))
  · refine Or.inr ⟨4, 1, φ, by decide, hφr, hφk, ?_⟩
    intro b hb
    have hperf : commutator ↥φ.range = ⊤ := by
      rw [hφr]
      exact hKcomp.2.2.1
    have hlabel' : GGHasLabel ⟨.twD, 4, 1⟩ (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
      rw [hφr]
      exact hlabel
    have hbN : b ∈ Subgroup.normalizer (φ.range : Set X) := by
      rw [hφr]
      exact hBNK hb
    exact ggPsiInnerDiag_of_cube_of_label_omegaMinus_two (by norm_num) (ggU .POmegaMinus 4 1).D φ
      hperf hlabel' hbN (hA.2 b (hBA hb))
  · refine Or.inl ⟨3, 2, φ, by decide, hφr, hφk, ?_⟩
    intro b hb
    let φSL : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) →* X := φ
    have hker : φSL.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := hφk
    have hbN : b ∈ Subgroup.normalizer (φSL.range : Set X) := by
      change b ∈ Subgroup.normalizer (φ.range : Set X)
      rw [hφr]
      exact hBNK hb
    have hF : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by decide)]
      norm_num
    change GGPsiInnerDiag (SpecialLinear.rootDatum 2 (GaloisField 2 2)) φSL b
    exact ggPsiInnerDiag_sl_of_cube_of_card_eq_two_or_four (by decide) (Or.inr hF)
      hker hbN (hA.2 b (hBA hb))

end CFSG.StandardType.RCKC1
