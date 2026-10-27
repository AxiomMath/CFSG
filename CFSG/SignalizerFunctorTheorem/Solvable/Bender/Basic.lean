module

public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.Solvable.Bender

variable {G : Type*} [Group G]

section Hyperplanes

variable [Finite G]

omit [Finite G] in
theorem le_card_of_mem_hyperplanes {p k : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hB : B ∈ Coprime.hyperplanes p A) (hlarge : p ^ (k + 1) ≤ Nat.card A) :
    p ^ k ≤ Nat.card B := by
  have hlarge' : p * p ^ k ≤ p * Nat.card B := by
    rw [← hB.2, ← pow_succ']
    exact hlarge
  exact Nat.le_of_mul_le_mul_left hlarge' hp.pos

theorem iSup_hyperplanes_inf_centralizer {p : ℕ} (hp : p.Prime) {A T : Subgroup G}
    (hA : IsElemAbelian p A) (hlarge : p ≤ Nat.card A)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hcop : Nat.Coprime p (Nat.card T)) :
    (⨆ B ∈ Coprime.hyperplanes p A, T ⊓ Subgroup.centralizer (B : Set G)) = T := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ :=
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA).exists_card_eq
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · rw [pow_zero] at hn
      have := hp.two_le
      omega
    · exact ⟨m, rfl⟩
  have hset : Coprime.hyperplanes p A = signalizerFunctorEk p m A := by
    ext B
    simp only [Coprime.hyperplanes, signalizerFunctorEk, Set.mem_ofPred_eq]
    rw [hn, pow_succ']
    exact and_congr_right fun _ => ⟨fun h => (Nat.eq_of_mul_eq_mul_left hp.pos h).symm,
      fun h => by rw [h]⟩
  rw [hset]
  exact CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p m hp A T hA
    hn.ge hAT hcop

end Hyperplanes

end CFSG.SignalizerFunctorTheorem.Solvable.Bender
