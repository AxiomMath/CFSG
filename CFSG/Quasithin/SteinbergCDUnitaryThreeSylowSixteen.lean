module

public import CFSG.Quasithin.SteinbergCDLinearThreeSylowSixteen
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.Quasithin.SteinbergCD

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem SUgram_one_eq_unitarySU (h : UnitaryFieldData p f K) :
    SUgram h.bar (1 : Matrix (Fin 3) (Fin 3) K) = unitarySU p f K 3 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K p := h.charP
  exact (SUgram_bar_one h 3).trans
    (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (card_eq_sq_of_unitaryFieldData h) 3)

theorem bar_one_apply (h : UnitaryFieldData p f K) (i j : Fin 3) :
    h.bar ((1 : Matrix (Fin 3) (Fin 3) K) j i) = (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · simp [one_apply, hij, Ne.symm hij]

theorem pow_three_eq_one_of_mem_unitaryScalars (h : UnitaryFieldData p f K)
    {z : unitarySU p f K 3} (hz : z ∈ unitaryScalars h 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc, hz⟩ := mem_unitaryScalars.1 hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hz, ← map_pow, hc, map_one, Subgroup.coe_one]

theorem ordProj_two_card_unitaryPSU_three (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    ordProj[2] (Nat.card (unitaryPSU h 3)) =
      ordProj[2] (p ^ f - 1) * ordProj[2] (p ^ f + 1) ^ 2 := by
  have := h.finite
  have hZ : Odd (Nat.card (unitaryScalars h 3)) := by
    rw [card_unitaryScalars h (by norm_num)]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  rw [ordProj_two_card_quotient_of_odd (unitaryScalars h 3) hZ, ← SUgram_one_eq_unitarySU h]
  exact ordProj_two_card_SUgram h hp2 (bar_one_apply h) (by rw [det_one]; exact one_ne_zero)

theorem ordProj_two_sub_one_of_mod_eight {q : ℕ} (hq : q % 8 = 5) : ordProj[2] (q - 1) = 4 := by
  obtain ⟨m, hm⟩ : ∃ m, q - 1 = 4 * (2 * m + 1) := ⟨q / 8, by omega⟩
  rw [hm, Nat.ordProj_mul 2 (by norm_num) (by omega), show (4 : ℕ) = 2 ^ 2 by norm_num,
    Nat.ordProj_self_pow Nat.prime_two, ordProj_two_of_odd (by exact ⟨m, rfl⟩), mul_one]

theorem exists_semidihedral_unitaryPSU_three (h : UnitaryFieldData p 1 K) (hp : p % 8 = 5) :
    ∃ a b : unitaryPSU h 3, orderOf a = 8 ∧ b ^ 2 = 1 ∧ b * a * b = a ^ 3 := by
  have hp2 : p ≠ 2 := by omega
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [det_one]; exact one_ne_zero
  have hr : ordProj[2] (p ^ 1 - 1) = 4 := by
    rw [pow_one]
    exact ordProj_two_sub_one_of_mod_eight hp
  obtain ⟨-, -, -, -, -, h1⟩ := odd_unitary_three_exact_coordinate_and_Sylow_models h hp2
    (bar_one_apply h) hdet (⊥ : Subgroup (SUgram h.bar (1 : Matrix (Fin 3) (Fin 3) K))) bot_le
  obtain ⟨⟨z, hz⟩, ⟨M, hM⟩, hmodel⟩ := h1 (by rw [pow_one]; omega)
  obtain ⟨u, τ, -, -, hu, hτ, hrel, -⟩ := hmodel M hM z hz
  rw [hr] at hu
  have hττ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left (by rw [← sq, hτ])
  have hrel' : τ * u * τ = u ^ 3 := by
    have h3 : u ^ (-(p ^ 1 : ℤ)) = u ^ (3 : ℤ) := by
      rw [← zpow_mod_orderOf, hu]
      conv_rhs => rw [← zpow_mod_orderOf, hu]
      congr 1
      push_cast
      simp only [pow_one]
      omega
    nth_rewrite 1 [← hττ]
    rw [hrel, h3, zpow_ofNat]
  let e := MulEquiv.subgroupCongr (SUgram_one_eq_unitarySU h)
  have hu' : orderOf (e u) = 8 := by rw [MulEquiv.orderOf_eq, hu]
  have hτ' : e τ ^ 2 = 1 := by rw [← map_pow, hτ, map_one]
  have hrel'' : e τ * e u * e τ = e u ^ 3 := by rw [← map_mul, ← map_mul, hrel', map_pow]
  obtain ⟨ha, hb, hab⟩ := semidihedral_quotient (Z := unitaryScalars h 3)
    (fun z hz => pow_three_eq_one_of_mem_unitaryScalars h hz) hu' hτ' hrel''
  exact ⟨_, _, ha, hb, hab⟩

theorem unitaryPSU_three_two_part (h : UnitaryFieldData p 1 K) (hp2 : p ≠ 2) :
    16 ≤ ordProj[2] (Nat.card (unitaryPSU h 3)) ∧
      (ordProj[2] (Nat.card (unitaryPSU h 3)) = 16 →
        ∃ a b : unitaryPSU h 3, orderOf a = 8 ∧ b ^ 2 = 1 ∧ b * a * b = a ^ 3) := by
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have hp1 : 1 < p := h.prime.one_lt
  rw [ordProj_two_card_unitaryPSU_three h hp2, pow_one]
  exact ⟨sixteen_le_mul_sq hodd hp1, fun h16 =>
    exists_semidihedral_unitaryPSU_three h (mod_eight_of_mul_sq_eq hodd hp1 h16)⟩

end CFSG.Quasithin.SteinbergCD
