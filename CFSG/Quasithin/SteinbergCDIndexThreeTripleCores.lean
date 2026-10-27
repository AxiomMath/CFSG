module

public import CFSG.Quasithin.SteinbergCDCentralThreeA6Centralizer
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.SteinbergCD

open CFSG Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H]

theorem mem_of_odd_orderOf_of_two_pow_mem {N : Subgroup H} {x : H} (hx : Odd (orderOf x))
    {k : ℕ} (h : x ^ 2 ^ k ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) := (Nat.coprime_two_left.2 hx).pow_left k
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hexp : (((2 ^ k : ℕ) : ℤ) * a + (orderOf x : ℤ) * b) = 1 := by
    rw [← hab]
    ring
  have h1 : x = (x ^ 2 ^ k) ^ a := by
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ (((2 ^ k : ℕ) : ℤ) * a + (orderOf x : ℤ) * b) := by rw [hexp]
      _ = (x ^ 2 ^ k) ^ a := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one,
          one_zpow, mul_one]
  rw [h1]
  exact zpow_mem h a

theorem mem_pResidual_of_odd {X : Type*} [Group X] {x : X} (hx : Odd (orderOf x)) :
    x ∈ pResidual 2 X := by
  simp only [pResidual, Subgroup.mem_iInf]
  intro N _ hpow
  obtain ⟨j, hj⟩ := hpow x
  exact mem_of_odd_orderOf_of_two_pow_mem hx hj

theorem pResidualOf_le_of {G N : Subgroup H} (hNG : N ≤ G)
    (hGN : G ≤ normalizer (N : Set H)) (h2 : ∀ g ∈ G, ∃ k : ℕ, g ^ 2 ^ k ∈ N) :
    pResidualOf 2 G ≤ N := by
  have : (N.subgroupOf G).Normal := (normal_subgroupOf_iff_le_normalizer hNG).mpr hGN
  have hle : pResidual 2 G ≤ N.subgroupOf G :=
    pResidual_le fun x => by
      obtain ⟨k, hk⟩ := h2 x x.2
      exact ⟨k, by rw [mem_subgroupOf]; exact hk⟩
  have := map_mono (f := G.subtype) hle
  rwa [subgroupOf_map_subtype, inf_eq_left.mpr hNG] at this

end SteinbergCD

open Subgroup SteinbergCD

end CFSG.Quasithin
