module

public import CFSG.Quasithin.Background.F7TwoInvL3TwoConj
public import CFSG.Quasithin.Background.F7TwoInvL3TwoOuter
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

theorem invAutGen_projectiveSL_three_even (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) :
    ∀ φ : MulAut (projectiveSL 3 K), φ * φ = 1 → φ ≠ 1 → InvAutGen (projectiveSL 3 K) φ := by
  intro φ hφ2 hφ1
  obtain ⟨f, hf2, hKf⟩ := id hK
  obtain ⟨A, σ, ε, hε, hφ⟩ := (automorphism_generation (K := K) (le_refl 3)).2 φ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hφ
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hφ
      subst hφ
      exact invAutGen_conjAut hK hφ2 hφ1
    · have hsq : (conjAut 3 K A * fieldAut 3 K σ) ^ 2 = 1 := by rw [pow_two, ← hφ]; exact hφ2
      obtain ⟨hev, hσpow, H, hH⟩ := even_linear_field_involution_descent (by omega) hKf
        (le_refl 3) A σ hσ hsq
      rw [hφ, hH]
      exact (InvAutGen.conj_iff _ _).1
        (invAutGen_fieldAut hK hσ (pow_pow_half_involutive hev hKf hσpow))
  · rw [pow_one] at hφ
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hφ
      have hsq : (conjAut 3 K A * dualAut 3 K) ^ 2 = 1 := by rw [pow_two, ← hφ]; exact hφ2
      obtain ⟨-, ⟨H, C, -, hconj, hcases⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms (by omega) hKf (le_refl 3) A
          hsq
      rcases hcases with ⟨hC, -⟩ | ⟨r, hr, -⟩
      · have hC1 : C = 1 := Units.ext hC
        rw [hφ, hconj, hC1, map_one, one_mul]
        exact (InvAutGen.conj_iff _ _).1 (invAutGen_dualAut hK)
      · omega
    · have hsq : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1 := by
        rw [pow_two, ← hφ]
        exact hφ2
      obtain ⟨hev, hσpow, H, hH⟩ := UnitaryHigher.linear_graph_field_involution_descent
        Nat.prime_two (by omega) hKf (le_refl 3) A σ hσ hsq
      rw [hφ, hH]
      exact (InvAutGen.conj_iff _ _).1
        (invAutGen_fieldAut_mul_dualAut hK (pow_pow_half_involutive hev hKf hσpow))

theorem invAutGen_of_statedPSL3_two {S : Type} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSL 3 2 f) :
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  exact invAutGen_of_mulEquiv_forall
    (e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm)
    (invAutGen_projectiveSL_three_even ⟨f, hf, hcard⟩)

theorem invAutGenFamL3Even : InvAutGenFamL3Even := fun _ _ _ _ hf h =>
  invAutGen_of_statedPSL3_two hf h

end CFSG.Quasithin.F7Two
