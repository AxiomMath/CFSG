module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows
import CFSG.LocalAnalysis.StandardType.ZS.MonomialWeyl
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialFrame

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem zsEqNegOneOfOrderTwo {ζ : (ZMod p)ˣ} (h : orderOf ζ = 2) : ζ = -1 := by
  have hsq : ζ ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one ζ
  have hζne : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h
    omega
  have hval : (ζ : ZMod p) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  rcases sq_eq_one_iff.mp hval with h1 | h1
  · exact absurd (Units.ext h1) hζne
  · exact Units.ext h1

theorem family_of_permMap_mem (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hA : AbsIrred p A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (b i) = c i • b (σ i))
    (hperm : ∀ σ, permMap p b σ ∈ A) : Family p A := by
  have hn2 : 2 ≤ n := by omega
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have h' : (0 : ℕ) = 1 := by simpa [i₀, i₁] using congrArg Fin.val h
    omega
  by_cases hsign : ∃ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A
  · obtain ⟨ζ, hζeven, hAeq⟩ := eq_g2mmn_of_permMap_mem hp b hgen hmon hperm hsign hi
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hζeven
    have hkpos : 0 < k := by
      have hpos : 0 < orderOf ζ := orderOf_pos ζ
      omega
    by_cases hk1 : k = 1
    · have hord2 : orderOf ζ = 2 := by rw [hk, hk1, mul_one]
      have hζneg : ζ = -1 := zsEqNegOneOfOrderTwo hord2
      refine Family.weyl ?_
      rw [hAeq, hζneg]
      exact linWeyl_g2mmn_neg_one hp hn2 b
    · have hk2 : 2 ≤ k := by omega
      exact Family.g2mmn b i₀ i₁ ζ k hi hk2 hk hAeq
  · have hsign' : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∉ A := by
      intro i hi_mem
      exact hsign ⟨i, hi_mem⟩
    obtain ⟨ζ, hAeq⟩ := eq_gmmn_of_permMap_mem hp b hgen hmon hperm hsign' hi
    by_cases hm1 : orderOf ζ = 1
    · have hζ1 : ζ = 1 := orderOf_eq_one_iff.mp hm1
      rw [hAeq, hζ1] at hA
      exact (not_absIrred_gmmn_one hn2 b i₀ i₁ hA).elim
    · by_cases hm2 : orderOf ζ = 2
      · have hζneg : ζ = -1 := zsEqNegOneOfOrderTwo hm2
        refine Family.weyl ?_
        rw [hAeq, hζneg]
        exact linWeyl_gmmn_neg_one hp hn b hi
      · have hm3 : 3 ≤ orderOf ζ := by
          have hpos : 0 < orderOf ζ := orderOf_pos ζ
          omega
        exact Family.gmmn b i₀ i₁ ζ (orderOf ζ) hi hm3 rfl hAeq

theorem family_of_imprimitive (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hA : AbsIrred p A) (himp : CFSG.Quasithin.SimsG4.IsImprimitiveOnV A) : Family p A := by
  obtain ⟨b, hmon⟩ := CFSG.StandardType.ggRC_monomial_of_imprimitive
    (n := Module.finrank (ZMod p) U) rfl A hA hgen himp
  obtain ⟨b', hmon', hperm', -⟩ := CFSG.StandardType.ggRC_monomial_frame hp b A hA hgen hmon
  exact family_of_permMap_mem hp h3 b' hgen hA hmon' hperm'

end CFSG.StandardType.ZS
