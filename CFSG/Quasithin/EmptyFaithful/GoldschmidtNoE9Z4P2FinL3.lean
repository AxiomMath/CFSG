module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.E9P2.FinL3

open Matrix

theorem card_sl3 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  have h := Matrix.card_SL_field (𝔽 := ZMod 2) 3
  rw [ZMod.card] at h
  rw [h]
  norm_num [Fin.prod_univ_succ]

theorem not_nine_dvd_card_sl3 : ¬ 9 ∣ Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rw [card_sl3]
  decide

private def cycM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

private theorem cycM_det : cycM.det = 1 := by decide +kernel

private theorem cycM_cube : cycM ^ 3 = 1 := by decide +kernel

private theorem cycM_ne_one : cycM ≠ 1 := by decide +kernel

private theorem eq_one_of_commute_cycM : ∀ w : Matrix (Fin 3) (Fin 3) (ZMod 2), w * w = 1 →
    w * cycM = cycM * w → w = 1 := by decide +kernel

private def cyc : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨cycM, cycM_det⟩

private theorem cyc_cube : cyc ^ 3 = 1 :=
  Subtype.ext (by rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one]; exact cycM_cube)

private theorem cyc_ne_one : cyc ≠ 1 := fun h => cycM_ne_one (congrArg Subtype.val h)

private theorem eq_one_of_commute_cyc {z : SpecialLinearGroup (Fin 3) (ZMod 2)} (hz : z * z = 1)
    (hc : z * cyc = cyc * z) : z = 1 := by
  refine Subtype.ext (eq_one_of_commute_cycM z ?_ ?_)
  · rw [← SpecialLinearGroup.coe_mul, hz, SpecialLinearGroup.coe_one]
  · have := congrArg Subtype.val hc
    rwa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul] at this

theorem eq_one_of_commute_of_order_three {a z : SpecialLinearGroup (Fin 3) (ZMod 2)} (ha : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hz : z * z = 1) (hc : z * a = a * z) : z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf cyc = 3 := orderOf_eq_prime cyc_cube cyc_ne_one
  have hP₀ : IsPGroup 3 (Subgroup.zpowers cyc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hidx : ¬ 3 ∣ (Subgroup.zpowers cyc).index := by
    have h := (Subgroup.zpowers cyc).card_mul_index
    rw [Nat.card_zpowers, hord, card_sl3] at h
    rw [show (Subgroup.zpowers cyc).index = 56 by omega]
    decide
  let S₀ : Sylow 3 (SpecialLinearGroup (Fin 3) (ZMod 2)) := hP₀.toSylow hidx
  have hordA : orderOf a = 3 := orderOf_eq_prime ha3 ha
  have hPa : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordA, pow_one])
  obtain ⟨Q, hQ⟩ := hPa.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) (ZMod 2)) S₀ Q
  have haQ : a ∈ (Q : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))) :=
    hQ (Subgroup.mem_zpowers a)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at haQ
  obtain ⟨p, hp, hpa⟩ := haQ
  have hpa' : g * p * g⁻¹ = a := by simpa [MulAut.smul_def, MulAut.conj_apply] using hpa
  have hp' : p ∈ Subgroup.zpowers cyc := hp
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp'
  have hk : cyc ^ k = cyc ^ (k % 3) := by
    have := zpow_mod_orderOf cyc k
    rw [hord] at this
    exact_mod_cast this.symm
  have hc' : z * (g * cyc ^ k * g⁻¹) = (g * cyc ^ k * g⁻¹) * z := by rw [hpa']; exact hc
  have hz' : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz]; group
  have hcomm : (g⁻¹ * z * g) * cyc ^ k = cyc ^ k * (g⁻¹ * z * g) := by
    calc (g⁻¹ * z * g) * cyc ^ k = g⁻¹ * (z * (g * cyc ^ k * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * cyc ^ k * g⁻¹) * z) * g := by rw [hc']
      _ = cyc ^ k * (g⁻¹ * z * g) := by group
  have hz1 : g⁻¹ * z * g = 1 := by
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rw [hk] at hcomm
    rcases hk3 with h0 | h1 | h2
    · exfalso
      apply ha
      rw [← hpa', hk, h0]
      group
    · rw [h1] at hcomm
      exact eq_one_of_commute_cyc hz' (by simpa using hcomm)
    · rw [h2] at hcomm
      have h4 : (g⁻¹ * z * g) * cyc = cyc * (g⁻¹ * z * g) := by
        have h5 := Commute.pow_right (show Commute (g⁻¹ * z * g) (cyc ^ (2 : ℤ)) from hcomm) 2
        have e : (cyc ^ (2 : ℤ)) ^ 2 = cyc := by
          rw [← zpow_natCast, ← zpow_mul, show (2 : ℤ) * ((2 : ℕ) : ℤ) = 3 + 1 by norm_num,
            zpow_add, zpow_ofNat, cyc_cube, one_mul, zpow_one]
        rw [e] at h5
        exact h5
      exact eq_one_of_commute_cyc hz' h4
  calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    _ = 1 := by rw [hz1]; group

end CFSG.Quasithin.E9P2.FinL3
