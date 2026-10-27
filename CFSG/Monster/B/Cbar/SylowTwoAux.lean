module

public import CFSG.Monster.B.Cbar.FourGroupBar
public import CFSG.Monster.B.Cbar.SylowControl
public import CFSG.Monster.B.Cbar.LocalE

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short

theorem Zstar_le_Jstar_subgroupOf : Zstar ≤ Jstar.subgroupOf Cgen := by
  rw [Zstar, Subgroup.zpowers_le]
  exact tStar_mem_Jstar

theorem ker_kappa_le_Jstar : kappa.ker ≤ Jstar.subgroupOf Cgen := by
  rw [ker_kappa]
  exact Zstar_le_Jstar_subgroupOf

theorem index_Jbar : Jbar.index = (Jstar.subgroupOf Cgen).index :=
  Subgroup.index_map_eq _ kappa_surjective ker_kappa_le_Jstar

theorem kappa_mem_Jbar_iff (g : Cgen) : kappa g ∈ Jbar ↔ (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar := by
  have h : Jbar.comap kappa = Jstar.subgroupOf Cgen := by
    rw [Jbar, Subgroup.comap_map_eq, sup_of_le_left ker_kappa_le_Jstar]
  rw [← Subgroup.mem_comap, h, Subgroup.mem_subgroupOf]

theorem natCard_Cgen : Nat.card Cgen = 2 * Nat.card Cbar := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zstar, natCard_Zstar, mul_comm]

theorem sylow_two_of_local (hC : Subgroup.centralizer {xbar} = Jbar)
    (hCE : Jbar ⊓ Subgroup.centralizer (Ebar : Set Cbar) = Subgroup.zpowers xbar)
    (hZE : (Subgroup.center Ebar).map Ebar.subtype = Subgroup.zpowers xbar)
    (hEp : IsPGroup 2 Ebar) (hcard : Nat.card Jbar = 2 ^ 41 * 161382375) :
    (∀ P : Sylow 2 Jbar, ∃ S : Sylow 2 Cbar,
      (S : Subgroup Cbar) = (P : Subgroup Jbar).map Jbar.subtype ∧
      (Subgroup.center (S : Subgroup Cbar)).map (S : Subgroup Cbar).subtype =
        Subgroup.zpowers xbar) ∧
    (∃ m : ℕ, Odd m ∧ Nat.card Cbar = 2 ^ 41 * m) ∧
    (∃ m : ℕ, Odd m ∧ Nat.card Cgen = 2 ^ 42 * m) ∧
    Jbar.index = (Jstar.subgroupOf Cgen).index ∧ Odd Jbar.index ∧
    (∀ g : Cbar, (∃ n : ℕ, g ^ 2 ^ n = 1) → ∃ c : Cbar, c * g * c⁻¹ ∈ Jbar) ∧
    (∀ g : Cgen, (∃ n : ℕ, g ^ 2 ^ n = 1) →
      ∃ c : Cgen, ((c * g * c⁻¹ : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : Ebar ≤ Subgroup.centralizer {xbar} := hC ▸ Ebar_le_Jbar
  have hQn : (Ebar.subgroupOf (Subgroup.centralizer {xbar})).Normal := by
    rw [hC]
    infer_instance
  have hCQ : Subgroup.centralizer {xbar} ⊓ Subgroup.centralizer (Ebar : Set Cbar) =
      Subgroup.zpowers xbar := by
    rw [hC]
    exact hCE
  obtain ⟨h1, h2, h3, -⟩ := prime_centralizer_sylow_control orderOf_xbar hQH hQn hEp hZE hCQ
  rw [hC] at h1 h2 h3
  have hodd : Odd Jbar.index := Nat.coprime_two_right.1 h2
  have hCbar : Nat.card Cbar = 2 ^ 41 * (161382375 * Jbar.index) := by
    rw [← Jbar.card_mul_index, hcard, mul_assoc]
  have hm : Odd (161382375 * Jbar.index) := (by decide : Odd 161382375).mul hodd
  refine ⟨h1, ⟨_, hm, hCbar⟩, ⟨_, hm, ?_⟩, index_Jbar, hodd, h3, ?_⟩
  · rw [natCard_Cgen, hCbar, pow_succ]
    ring
  · intro g ⟨n, hn⟩
    obtain ⟨c, hc⟩ := h3 (kappa g) ⟨n, by rw [← map_pow, hn, map_one]⟩
    obtain ⟨c₀, rfl⟩ := kappa_surjective c
    refine ⟨c₀, (kappa_mem_Jbar_iff _).1 ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact hc

end CFSG.Monster.B
