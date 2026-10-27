module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup Matrix CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement LinearAlgebra.Projectivization

theorem exists_rootGrp_eq_map_sylow {Y : Type*} [Group Y] [Finite Y] {k : Type*} [Field k]
    [Finite k] {n : ℕ} (hn : 1 ≤ n) (hk : Nat.card k = 2 ^ n)
    (ρ : Y →* SpecialLinearGroup (Fin 2) k) (hρ : Function.Surjective ρ) (S : Sylow 2 Y) :
    ∃ ℓ : ℙ k (Fin 2 → k), (S : Subgroup Y).map ρ = rootGrp ℓ := by
  have hq1 : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
    intro hd
    have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h3 : 0 < (2 ^ n) ^ 2 := by positivity
    omega
  have hfac : (2 ^ n * ((2 ^ n) ^ 2 - 1)).factorization 2 = n := by
    have hne1 : 2 ^ n ≠ 0 := by positivity
    have hne2 : (2 ^ n) ^ 2 - 1 ≠ 0 := by
      intro h0
      rw [h0] at hq1
      exact hq1 (dvd_zero 2)
    rw [Nat.factorization_mul hne1 hne2]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hq1]
  have hsyl : Nat.card ((Sylow.mapSurjective hρ S : Sylow 2 (SpecialLinearGroup (Fin 2) k)) :
      Subgroup (SpecialLinearGroup (Fin 2) k)) = Nat.card k := by
    rw [Sylow.card_eq_multiplicity, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk,
      hfac]
  rw [← Sylow.coe_mapSurjective hρ S]
  exact exists_point_eq_rootGrp Nat.prime_two hk hsyl

variable {G : Type*} [Group G]

end CFSG.Quasithin.SteinbergBS
