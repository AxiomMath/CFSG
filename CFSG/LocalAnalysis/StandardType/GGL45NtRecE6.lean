module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
import CFSG.LocalAnalysis.StandardType.GGL45E67Center
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggL45NtRecE6_inner_of_isPElt {K : Type} [Field K]
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {φ : MulAut (TableBExc.RecipeGroup .E6 K)}
    (hφ : φ ∈ TableBExc.RecipeID .E6 K) (hφp : GGL45IsPElt p φ) :
    ∃ r : TableBExc.RecipeGroup .E6 K, φ = MulAut.conj r := by
  set N := (MulAut.conj : TableBExc.RecipeGroup .E6 K →*
    MulAut (TableBExc.RecipeGroup .E6 K)).range with hN
  obtain ⟨k, hk⟩ := hφp
  have h3 : (φ : MulAut (TableBExc.RecipeGroup .E6 K) ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact TableBExc.pow_three_mem_inn_of_mem_recipeID_E6 hφ
  have hp' : (φ : MulAut (TableBExc.RecipeGroup .E6 K) ⧸ N) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (p ^ k) 3 :=
    ((Nat.coprime_primes hp Nat.prime_three).2 hp3).pow_left k
  have h1 : orderOf (φ : MulAut (TableBExc.RecipeGroup .E6 K) ⧸ N) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hp')
      (orderOf_dvd_of_pow_eq_one h3)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  obtain ⟨r, hr⟩ := h1
  exact ⟨r, hr.symm⟩

theorem ggL45NtRecOn_e6 :
    GGL45NtRecOn GGL45NtFamExE6 := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hfam, hE6⟩ := hS
  subst hE6
  have hp3 : p ≠ 3 := hfam.1
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hField, hFinite, hK, hQ', fun _ _ => ⟨?_, ?_, ?_⟩⟩
  · intro r
    exact Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
  · intro u hu huP
    obtain ⟨r, hr⟩ := ggL45NtRecE6_inner_of_isPElt hp hp3 hu huP
    exact ⟨r, hr⟩
  · exact ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3

theorem ggL45NtRecOn_E6_odd :
    GGL45NtRecOn fun _ lab => lab.tag = .E6 ∧ Odd lab.n := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hE6, hodd⟩ := hS
  dsimp only at hE6 hodd
  subst hE6
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
  letI : Field K := hf
  letI : Finite K := hfin
  haveI : CharP K 2 := charP_two_of_card hK
  have hmod : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hodd
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hndvd : ¬ 3 ∣ 2 ^ n - 1 := by
    generalize 2 ^ n = x at hmod
    omega
  have hunits : Nat.card Kˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, hK]
  have hcop3 : Nat.Coprime (Nat.card Kˣ) 3 := by
    rw [hunits, Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hndvd
  have hcube : ∀ s : Kˣ, ∃ u : Kˣ, u ^ 3 = s := fun s =>
    ⟨(powCoprime hcop3).symm s, by rw [← powCoprime_apply hcop3, Equiv.apply_symm_apply]⟩
  have hT : TableB.torusSubgroup (LargeEvenCartanE 6) K = ⊤ :=
    TableB.torusSubgroup_eq_top_of_mul_eq_smul (LargeEvenCartanE 6) K TableB.cartanE6_adj hcube
  have hgcd : Nat.Coprime p (Nat.gcd 3 (Nat.card K - 1)) := by
    have h1 : Nat.gcd 3 (Nat.card K - 1) = 1 := by
      rw [hK]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hndvd
    rw [h1]
    exact Nat.coprime_one_right p
  refine ⟨K, hf, hfin, hK, hQ, fun _ _ => ⟨?_, ?_, ?_⟩⟩
  · intro r
    exact Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
  · intro u hu _
    obtain ⟨r, hr⟩ := chevIDImage_subset_inn_of_top (K := K) (τ := .E6) hT hu
    exact ⟨r, hr.symm⟩
  · exact ggCenterPrime_recipe_E6_of_coprime hp hp2 hgcd

end CFSG.StandardType
