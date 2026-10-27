module

public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod
import CFSG.LocalAnalysis.WeakClosure81.SU3RankModel
import CFSG.LocalAnalysis.WeakClosure81.SU3RankRoots
import CFSG.LocalAnalysis.WeakClosure81.SU3RankTorusModel
import CFSG.LocalAnalysis.WeakClosure81.SU3RankGeneric
import CFSG.LocalAnalysis.WeakClosure81.SU3RankEightCase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic

theorem two_mul_le_modCommRank_permSU_swap_of_injective {n : ℕ} {F₀ : Type} [Field F₀]
    [Finite F₀] [CharP F₀ 2] (hn : 1 ≤ n) (hcard : Nat.card F₀ = (2 ^ n) ^ 2)
    {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Finite F]
    (σ : ↥(StatedSU 3 (2 ^ n) F₀) →* LGL 2 F) (hσ : Function.Injective σ) :
    2 * n ≤ modCommRank (σ (permSU n F₀ (Equiv.swap 0 1))) := by
  have hker : ∀ x, σ x = 1 → (x : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀ := by
    intro x hx
    have hx1 : x = 1 := by
      apply hσ
      rw [hx, map_one]
    simpa [hx1] using Subgroup.one_mem (StatedScalars (Fin 3) F₀)
  rcases eq_or_lt_of_le hn with h1 | h2
  ·
    obtain rfl : n = 1 := h1.symm
    obtain ⟨ν, hν⟩ := exists_orderOf_eq_of_dvd_two_pow_add_one (n := 1) (F₀ := F₀) hcard
      (m := 3) (by norm_num)
    have hν' : orderOf ν = 3 ^ 1 := hν
    have hinj : ∀ a b : rootsOfUnity (2 ^ 1 + 1) F₀, a ^ 3 = 1 → b ^ 3 = 1 →
        σ (diagSU 1 F₀ (a, b)) = 1 → a = 1 ∧ b = 1 := by
      intro a b _ _ hab
      have hx : diagSU 1 F₀ (a, b) = diagSU 1 F₀ 1 := by
        apply hσ
        rw [hab, map_one (diagSU 1 F₀), map_one]
      have hab' : (a, b) = 1 := diagSU_injective hx
      exact ⟨by simpa using congrArg Prod.fst hab', by simpa using congrArg Prod.snd hab'⟩
    have hle := orderOf_two_le_modCommRank_permSU_swap (n := 1) (F₀ := F₀) (ℓ := 3) (k := 1)
      Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2) (le_refl 1) (ν := ν) hν' σ hinj
    have h2ord : orderOf (2 : ZMod (3 ^ 1)) = 2 :=
      orderOf_eq_prime (by decide) (by decide)
    rw [h2ord] at hle
    simpa using hle
  · rcases eq_or_ne n 3 with h3 | h3
    ·
      subst n
      have hsix := six_le_modCommRank_permSU_swap hcard σ hker
      simpa using hsix
    ·
      exact two_mul_le_modCommRank_permSU_swap_of_ne_three (n := n) (F₀ := F₀)
        (by omega) h3 hcard σ hker

end CFSG.LocalAnalysis.WeakClosure81

end
