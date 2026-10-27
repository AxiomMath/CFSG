module

public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod
import CFSG.LocalAnalysis.WeakClosure81.SU3RankModel
import CFSG.LocalAnalysis.WeakClosure81.SU3RankRoots
import CFSG.LocalAnalysis.WeakClosure81.SU3RankTorusModel
import CFSG.LocalAnalysis.WeakClosure81.SU3RankEightModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic

private theorem orderOf_two_zmod_nine : orderOf (2 : ZMod (3 ^ 2)) = 6 := by
  have h : orderOf (2 : ZMod 9) = 6 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 6)]
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  simpa using h

private theorem exists_pow_eq_of_cube_eq_one {F₀ : Type} [Field F₀] [Finite F₀] {a b : F₀ˣ}
    (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (hb : b ^ 3 = 1) : ∃ j : ℕ, a ^ j = b := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hprim : IsPrimitiveRoot a 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime ha ha1)
  have hb' : b ∈ rootsOfUnity 3 F₀ := by
    rw [mem_rootsOfUnity]
    exact hb
  have hmem : b ∈ Subgroup.zpowers a := by
    rw [hprim.zpowers_eq]
    exact hb'
  exact (Submonoid.mem_powers_iff b a).mp (mem_powers_iff_mem_zpowers.mpr hmem)

theorem six_le_modCommRank_permSU_swap {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2]
    (hcard : Nat.card F₀ = (2 ^ 3) ^ 2) {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    [Finite F] (σ : ↥(StatedSU 3 (2 ^ 3) F₀) →* LGL 2 F)
    (hσ : ∀ x, σ x = 1 → (x : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀) :
    6 ≤ modCommRank (σ (permSU 3 F₀ (Equiv.swap 0 1))) := by
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd_two_pow_add_one (n := 3) (m := 9)
    hcard (by norm_num : 9 ∣ 2 ^ 3 + 1)
  by_cases hZ : ∀ a : rootsOfUnity (2 ^ 3 + 1) F₀, a ^ 3 = 1 →
      σ (diagSU 3 F₀ (a, a)) = 1
  · exact six_le_modCommRank_permSU_swap_of_center (ζ := ζ) hζ σ hσ hZ
  · push Not at hZ
    obtain ⟨a₀, ha₀, ha₀σ⟩ := hZ
    have hinj : ∀ a b : rootsOfUnity (2 ^ 3 + 1) F₀, a ^ 3 = 1 → b ^ 3 = 1 →
        σ (diagSU 3 F₀ (a, b)) = 1 → a = 1 ∧ b = 1 := by
      intro a b ha hb hσab
      have hmem : ((diagSU 3 F₀ (a, b) : ↥(StatedSU 3 (2 ^ 3) F₀)) : GL (Fin 3) F₀) ∈
          StatedScalars (Fin 3) F₀ := hσ (diagSU 3 F₀ (a, b)) hσab
      obtain ⟨hab, ha3⟩ :=
        (diagSU_mem_statedScalars_iff (n := 3) (F₀ := F₀) (a, b)).mp hmem
      have hab' : a = b := hab
      subst b
      have ha_one : a = 1 := by
        by_contra ha1
        have ha3' : (a : F₀ˣ) ^ 3 = 1 := by
          simpa using congrArg (fun x : rootsOfUnity (2 ^ 3 + 1) F₀ => (x : F₀ˣ)) ha3
        have ha1' : (a : F₀ˣ) ≠ 1 := fun h => ha1 (Subtype.ext (by simpa using h))
        have ha₀3' : (a₀ : F₀ˣ) ^ 3 = 1 := by
          simpa using congrArg (fun x : rootsOfUnity (2 ^ 3 + 1) F₀ => (x : F₀ˣ)) ha₀
        obtain ⟨j, hj⟩ := exists_pow_eq_of_cube_eq_one ha3' ha1' ha₀3'
        have hpow : a ^ j = a₀ := by
          apply Subtype.ext
          simpa using hj
        have hdiag : diagSU 3 F₀ (a₀, a₀) = (diagSU 3 F₀ (a, a)) ^ j := by
          rw [← hpow, ← map_pow]
          congr 1
        have hone : σ (diagSU 3 F₀ (a₀, a₀)) = 1 := by
          rw [hdiag, map_pow, hσab]
          simp
        exact ha₀σ hone
      exact ⟨ha_one, ha_one⟩
    have hle := orderOf_two_le_modCommRank_permSU_swap (n := 3) (ℓ := 3) (k := 2)
      (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : 1 ≤ 2)
      (ν := ζ) (by simpa using hζ) σ hinj
    rw [orderOf_two_zmod_nine] at hle
    exact hle

end CFSG.LocalAnalysis.WeakClosure81

end
