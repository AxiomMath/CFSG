module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.Vol2.F134LieU3

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.F134.LieU3 CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem not_dvd_twentyFive_mul_cube {q : ℕ} (hq : 3 ≤ q) : ¬ q ^ 3 + 1 ∣ 25 * q ^ 3 := by
  intro hdvd
  have hcop : (q ^ 3 + 1).Coprime (q ^ 3) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have h25 := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
  have : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  omega

theorem facts134Five_psu3Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n := by
  intro n A _ _ L P T hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 3 ≤ 2 ^ n := by
    obtain ⟨-, hn1, -, hne⟩ := hL.1
    have hn : 2 ≤ n := by
      by_contra hlt
      obtain rfl : n = 1 := by omega
      exact hne rfl
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hS := E25Config.isSylowTwoOf_inf hcfg
  obtain ⟨K, _, h, Φ, hΦ, hrange, hTU⟩ := exists_perm_comap_rkOneUStar_eq hL
    ((hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2)
  replace hTU : (rkOneUStar h).comap Φ = (T ⊓ L).subgroupOf L := hTU
  have hcardU : Nat.card (T ⊓ L : Subgroup A) = (2 ^ n) ^ 3 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, ← hTU,
      ← Subgroup.card_map_of_injective hΦ, Subgroup.map_comap_eq, hrange,
      inf_eq_right.2 (rkOneUStar_le_rkOneG h), card_rkOneUStar h]
  have hUH : rkOneUStar h ≤ ((P ⊔ T ⊓ L).subgroupOf L).map Φ := by
    intro x hx
    have hx' : x ∈ Φ.range := by
      rw [hrange]
      exact rkOneUStar_le_rkOneG h hx
    obtain ⟨y, rfl⟩ := hx'
    have hy : y ∈ (rkOneUStar h).comap Φ := hx
    rw [hTU] at hy
    exact ⟨y, Subgroup.subgroupOf_mono _ le_sup_right hy, rfl⟩
  have hcardH : Nat.card (((P ⊔ T ⊓ L).subgroupOf L).map Φ) = 25 * (2 ^ n) ^ 3 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E25Config.sup_inf_le hcfg)).toEquiv,
      E25Config.card_sup_inf hcfg, hcardU]
  have hfix := le_stabilizer_infL_of_not_dvd h hUH (by
    rw [hcardH]
    exact not_dvd_twentyFive_mul_cube hq)
  have hQinf : (P.subgroupOf L).map Φ ≤ rkOneGInf h := fun x hx =>
    ⟨hrange ▸ Subgroup.map_le_range Φ _ hx,
      hfix (Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_left) hx)⟩
  have hQcard : Nat.card ((P.subgroupOf L).map Φ) = 25 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  have hQexp : ∀ x ∈ (P.subgroupOf L).map Φ, x ^ 5 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy5 : y ^ 5 = 1 :=
      Subtype.ext (by simpa using hcfg.exp y (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy5, map_one]
  exact not_isCyclic_of_card_twentyFive hQcard hQexp
    (isCyclic_of_le_rkOneGInf h hQinf (by rw [hQcard]; norm_num))

end CFSG.Quasithin.S146zY
