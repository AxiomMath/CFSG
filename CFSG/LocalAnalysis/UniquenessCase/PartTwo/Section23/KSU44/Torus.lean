module

public import CFSG.ClassicalGroups.UnitaryFlag.SplitTorus


public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open

variable {K : Type} [Field K]

theorem splitInv_rootsOfUnity_three (hK : UnitaryFieldData 2 2 K) :
    SplitInv hK (rootsOfUnity 3 K) := by
  intro a
  have h3 : ((a : Kˣ) : K) ^ 3 = 1 := by
    have h := (mem_rootsOfUnity 3 (a : Kˣ)).mp a.2
    simpa using congrArg (fun u : Kˣ => (u : K)) h
  have hpow : ((a : Kˣ) : K) ^ 4 = ((a : Kˣ) : K) := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num]
    rw [pow_succ, h3, one_mul]
  rw [hK.bar_apply]
  exact hpow

theorem card_rootsOfUnity_three (hK : UnitaryFieldData 2 2 K) :
    Nat.card (rootsOfUnity 3 K) = 3 := by
  haveI : Finite K := hK.finite
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply le_antisymm
  · simpa using card_rootsOfUnity K 3
  · have hunits : Nat.card Kˣ = 15 := by
      rw [Nat.card_units, hK.card]
      norm_num
    have hdvd : 3 ∣ Nat.card Kˣ := by rw [hunits]; norm_num
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
    have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    have hle : Subgroup.zpowers ζ ≤ rootsOfUnity 3 K :=
      Subgroup.zpowers_le_of_mem ((mem_rootsOfUnity 3 ζ).mpr hζ3)
    have hcard := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hζ] at hcard
    exact hcard

@[expose] noncomputable def torusE (hK : UnitaryFieldData 2 2 K) : Subgroup (hypSU hK 2 0) :=
  (splitTorusHom hK 2 0 (rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK)).range

theorem torusE_isElemAbelian (hK : UnitaryFieldData 2 2 K) : IsElemAbelian 3 (torusE hK) := by
  have hexp : ∀ a : rootsOfUnity 3 K, a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    simpa using (mem_rootsOfUnity 3 (a : Kˣ)).mp a.2
  exact splitTorusHom_range_isElemAbelian (r := 2) (ε := 0)
    (μ := rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK) hexp

theorem card_torusE (hK : UnitaryFieldData 2 2 K) : Nat.card ↥(torusE hK) = 9 := by
  show Nat.card ↥((splitTorusHom hK 2 0 (rootsOfUnity 3 K)
    (splitInv_rootsOfUnity_three hK)).range) = 9
  rw [splitTorusHom_range_card (r := 2) (ε := 0) (μ := rootsOfUnity 3 K)
    (splitInv_rootsOfUnity_three hK), card_rootsOfUnity_three hK]
  norm_num

theorem torusE_le_normalizer (hK : UnitaryFieldData 2 2 K) :
    torusE hK ≤ Subgroup.normalizer (hypUnitriangular hK 2 0 : Set (hypSU hK 2 0)) := by
  rw [_root_.CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular
    (r := 2) (ε := 0) hK (by norm_num) (by norm_num)]
  rintro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  exact hypTorus_le_hypBorel hK (splitTorusHom_mem_hypTorus (splitInv_rootsOfUnity_three hK) y)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
