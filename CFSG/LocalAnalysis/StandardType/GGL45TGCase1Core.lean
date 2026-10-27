module

public import CFSG.LocalAnalysis.StandardType.GGL45TAHFour
public import CFSG.LocalAnalysis.StandardType.GGL45NtClLinCore
public import CFSG.LocalAnalysis.StandardType.GGL45NtClUniCore

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly

theorem ggL45NtCoreOn_famTypeACase1 : GGL45NtCoreOn GGL45FamTypeACase1 := by
  intro p hp hp2 lab hlab _ hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hd : 3 ≤ rank + 1 := ggL45FamTypeA_three_le hp hp2 hS.1
  obtain ⟨⟨htag, -⟩, hq⟩ := hS
  rcases htag with ht | ht <;> dsimp only at ht <;> subst ht
  · dsimp only [GGL45Eps] at hq
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    have hq' : ¬ p ∣ Fintype.card K - 1 := by
      intro h
      apply hq
      rw [← Nat.card_eq_fintype_card, hK] at h
      have h1 : ((2 ^ n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ n - 1 := by
        rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
      rw [← h1]
      exact Int.natCast_dvd_natCast.mpr h
    exact CFSG.HardMathSupport.C14Cl.ntCore_lin (d := rank + 1) hd hp hp2 (Or.inr hq')
  · dsimp only [GGL45Eps] at hq
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (show 1 ≤ 2 * n by have hn1 : 1 ≤ n := hlab.1; omega) (by rw [hK, ← pow_mul, mul_comm])
    have hK' : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    have hq' : ¬ p ∣ 2 ^ n + 1 := by
      intro h
      apply hq
      have h1 : (((2 ^ n + 1 : ℕ)) : ℤ) = (2 : ℤ) ^ n - -1 := by push_cast; ring
      rw [← h1]
      exact Int.natCast_dvd_natCast.mpr h
    exact CFSG.HardMathSupport.C14Cl.ntCore_uni (d := rank + 1) (q := 2 ^ n) hd hp hp2
      (Or.inr hq') hK'

end CFSG.StandardType.GGL45TG
