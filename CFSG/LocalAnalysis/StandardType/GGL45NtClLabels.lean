module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtClRecipes
public import CFSG.LocalAnalysis.StandardType.GGL45NtClLinCore
public import CFSG.LocalAnalysis.StandardType.GGL45NtClUniCore
public import CFSG.LocalAnalysis.StandardType.GGL45NtClOrthCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtCoreOn_lin : GGL45NtCoreOn GGL45NtFamLin := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hnt, hvac, _hexc⟩ := hS.1
  rcases hS.2 with hA | ⟨hD, hr3⟩
  · subst hA
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    have hrne : rank ≠ 1 := fun h => hvac (Or.inl ⟨rfl, h⟩)
    have hrank1 : 1 ≤ rank := hlab.2.1
    exact CFSG.HardMathSupport.C14Cl.ntCore_lin (d := rank + 1) (by omega) hp hp2 (Or.inl hnt)
  · subst hD
    subst hr3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_pos rfl] at hQ ⊢
    dsimp only [LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    have hpd : ¬ p ∣ 4 := by
      intro h
      have h42 : (2 : ℕ) ^ 2 = 4 := by norm_num
      have h2dvd : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (h42 ▸ h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)
    exact CFSG.HardMathSupport.C14Cl.ntCore_lin (d := 4) (by norm_num) hp hp2 (Or.inl hpd)

theorem ggL45NtCoreOn_uni : GGL45NtCoreOn GGL45NtFamUni := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  rcases hS.2 with htag | ⟨htag, hrank⟩
  · subst htag
    have hpd : ¬ p ∣ rank + 1 := hS.1.1
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (show 1 ≤ 2 * n by have hn1 : 1 ≤ n := hlab.1; omega) (by rw [hK, ← pow_mul, mul_comm])
    have hK' : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    exact CFSG.HardMathSupport.C14Cl.ntCore_uni (d := rank + 1) (q := 2 ^ n)
      (Nat.succ_le_succ hlab.2.1) hp hp2 (Or.inl hpd) hK'
  · subst htag
    subst hrank
    have hpd : ¬ p ∣ 4 := by
      intro hdvd
      have h2 : p ∣ 2 ^ 2 := by simpa using hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (show 1 ≤ 2 * n by have hn1 : 1 ≤ n := hlab.1; omega) (by rw [hK, ← pow_mul, mul_comm])
    have hK' : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    exact CFSG.HardMathSupport.C14Cl.ntCore_uni (d := 4) (q := 2 ^ n) (by norm_num) hp hp2
      (Or.inl hpd) hK'

theorem ggL45NtCoreOn_sp : GGL45NtCoreOn GGL45NtFamSp := by
  intro p hp hp2 lab hlab hkg hSp Q hraw
  obtain ⟨t, l, n⟩ := lab
  rcases hSp.2 with ht | ht <;> dsimp only at ht <;> subst ht <;>
  · dsimp only [LargeEvenRawDatum] at hraw ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (m := l) (N := 2 ^ n)
      (Q := GGL45NtCore p) (fun K _ _ hK => ?_) hraw
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    exact CFSG.HardMathSupport.C14Cl.ntCore_sp hlab.2.1 hp hp2

theorem ggL45NtCoreOn_orth : GGL45NtCoreOn GGL45NtFamOrth := by
  intro p hp hp2 lab hlab _hkg hS
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨-, hvac, hexc⟩, hlin, huni, hsp⟩ := hS
  have ht : t = .D ∨ t = .twD := by
    cases t <;> simp_all [GGL45NtVacLabel, GGL45NtExcLabel, GGL45NtLinLabel,
      GGL45NtUniLabel, GGL45NtSpLabel]
  have h4 : 4 ≤ l := by
    rcases ht with h | h
    · have hlab' := hlab
      rw [h] at hlab'
      dsimp only [LargeEvenInLambda2] at hlab'
      have h3 : l ≠ 3 := by
        intro hl3
        exact hlin (by rw [h]; exact Or.inr ⟨rfl, hl3⟩)
      omega
    · have hlab' := hlab
      rw [h] at hlab'
      dsimp only [LargeEvenInLambda2] at hlab'
      have h2 : l ≠ 2 := by
        intro hl2
        exact hvac (by rw [h]; exact Or.inr (Or.inl ⟨rfl, hl2⟩))
      have h3 : l ≠ 3 := by
        intro hl3
        exact huni (by rw [h]; exact Or.inr ⟨rfl, hl3⟩)
      omega
  rcases ht with h | h
  · subst h
    refine largeEvenLabelAll_omegaPlus (P := GGL45NtCore p) rfl h4 ?_
    intro K _ _ _ hK
    haveI := Fintype.ofFinite K
    exact CFSG.HardMathSupport.C14Cl.ntCore_omegaPlus (by omega) hp hp2
  · subst h
    refine largeEvenLabelAll_omegaMinus (P := GGL45NtCore p) rfl h4 ?_
    intro K _ _ _ hK b c hbc
    haveI := Fintype.ofFinite K
    exact CFSG.HardMathSupport.C14Cl.ntCore_omegaMinus (m := l - 1) (by omega) hp hp2 b c hbc

theorem ggL45NtCoreOn_cl : GGL45NtCoreOn GGL45NtFamCl :=
  (ggL45NtCoreOn_lin.union (ggL45NtCoreOn_uni.union (ggL45NtCoreOn_sp.union
    ggL45NtCoreOn_orth))).antitone ggL45NtFamCl_cover

end CFSG.StandardType
