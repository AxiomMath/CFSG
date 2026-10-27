module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Odd-order normalizers of order-three subgroups -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An odd-order subgroup normalizing a subgroup of cardinality three
centralizes it. -/
public theorem odd_subgroup_le_centralizer_of_le_normalizer_card_three
    {G : Type u} [Group G] [Finite G]
    (B F : Subgroup G)
    (hBodd : Odd (Nat.card B))
    (hFcard : Nat.card F = 3)
    (hBnorm : B ≤ Subgroup.normalizer (F : Set G)) :
    B ≤ Subgroup.centralizer (F : Set G) := by
  classical
  let i : B →* Subgroup.normalizer (F : Set G) :=
    Subgroup.inclusion hBnorm
  let rho : B →* MulAut F := F.normalizerMonoidHom.comp i
  have hFcyc : IsCyclic F := isCyclic_of_prime_card hFcard
  let : IsCyclic F := hFcyc
  have hAutcard : Nat.card (MulAut F) = 2 := by
    rw [IsCyclic.card_mulAut, hFcard, Nat.totient_prime Nat.prime_three]
  have hrange_dvd_B : Nat.card rho.range ∣ Nat.card B :=
    Subgroup.card_range_dvd rho
  have hrange_odd : Odd (Nat.card rho.range) :=
    Odd.of_dvd_nat hBodd hrange_dvd_B
  have hrange_dvd_Aut : Nat.card rho.range ∣ Nat.card (MulAut F) :=
    Subgroup.card_subgroup_dvd_card rho.range
  have hrange_card : Nat.card rho.range = 1 := by
    rw [hAutcard] at hrange_dvd_Aut
    rcases (Nat.dvd_prime Nat.prime_two).mp hrange_dvd_Aut with h1 | h2
    · exact h1
    · rw [h2] at hrange_odd
      norm_num at hrange_odd
  have hrange_bot : rho.range = ⊥ :=
    (Subgroup.eq_bot_iff_card (H := rho.range)).mpr hrange_card
  intro b hb
  let bB : B := ⟨b, hb⟩
  let bN : Subgroup.normalizer (F : Set G) :=
    ⟨b, hBnorm hb⟩
  have hrho : rho bB = 1 := by
    have hmem : rho bB ∈ rho.range := ⟨bB, rfl⟩
    rw [hrange_bot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbker : bN ∈ F.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    exact hrho
  rw [Subgroup.normalizerMonoidHom_ker] at hbker
  exact hbker

end CFSG.GorensteinWalter
