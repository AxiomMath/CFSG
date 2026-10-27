module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

theorem zpow_eq_one_of_conj_mem {X : Type*} [Group X] {w v y : X} {k : ℤ}
    (hwv : w * v = v * w) (hw3 : w ^ 3 = 1) (hv3 : v ^ 3 = 1)
    (hwnot : w ∉ Subgroup.zpowers v)
    (hyw : y * w * y⁻¹ = w) (hyv : y * v * y⁻¹ = v⁻¹)
    (hyu : y * (w * v ^ k) * y⁻¹ ∈ Subgroup.zpowers (w * v ^ k)) :
    v ^ k = 1 := by
  have hconj : y * (w * v ^ k) * y⁻¹ = w * (v ^ k)⁻¹ := by
    calc y * (w * v ^ k) * y⁻¹ = (y * w * y⁻¹) * (y * v * y⁻¹) ^ k := by
          rw [conj_zpow]; group
      _ = w * (v ^ k)⁻¹ := by rw [hyw, hyv, inv_zpow]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyu
  rw [hconj] at hm
  have hcomm : Commute w (v ^ k) := Commute.zpow_right (show Commute w v from hwv) k
  have hx3 : (v ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv3, one_zpow]
  have hw3z : w ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hw3
  have hx3z : (v ^ k) ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hx3
  have hm2 : w ^ m * (v ^ k) ^ m = w * (v ^ k)⁻¹ := (hcomm.mul_zpow m).symm.trans hm
  rw [zpow_eq_zpow_emod m hw3z, zpow_eq_zpow_emod m hx3z] at hm2
  have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr with h | h | h <;> rw [h] at hm2
  ·
    simp only [zpow_zero, mul_one] at hm2
    have hwk : w = v ^ k := mul_inv_eq_one.mp hm2.symm
    exact (hwnot (Subgroup.mem_zpowers_iff.mpr ⟨k, hwk.symm⟩)).elim
  ·
    simp only [zpow_one] at hm2
    have h1 : v ^ k = (v ^ k)⁻¹ := mul_left_cancel hm2
    have h2 : v ^ k * v ^ k = 1 := by
      calc v ^ k * v ^ k = v ^ k * (v ^ k)⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel _
    have h3 : (v ^ k) ^ 3 = v ^ k := by rw [pow_three, h2, mul_one]
    exact h3.symm.trans hx3
  ·
    simp only [zpow_two] at hm2
    have h4 : v ^ k * (v ^ k * v ^ k) = 1 := by rw [← pow_three]; exact hx3
    have hinv : (v ^ k)⁻¹ = v ^ k * v ^ k := inv_eq_of_mul_eq_one_right h4
    rw [hinv] at hm2
    have h5 : w * w = w := mul_right_cancel hm2
    have hw1 : w = 1 := mul_left_cancel (h5.trans (mul_one w).symm)
    exact (hwnot (Subgroup.mem_zpowers_iff.mpr ⟨0, by rw [zpow_zero]; exact hw1.symm⟩)).elim

theorem conj_mem_sup_zpowers {X : Type*} [Group X] {s t y : X}
    (hs : y * s * y⁻¹ ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers t)
    (ht : y * t * y⁻¹ ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers t)
    {z : X} (hz : z ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers t) :
    y * z * y⁻¹ ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers t := by
  have hle : Subgroup.zpowers s ⊔ Subgroup.zpowers t ≤
      (Subgroup.zpowers s ⊔ Subgroup.zpowers t).comap (MulAut.conj y).toMonoidHom :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr hs))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr ht))
  exact Subgroup.mem_comap.mp (hle hz)

theorem mem_normalizer_sup_of {X : Type*} [Group X] [Finite X] {U V : Subgroup X} {y : X}
    (hU : ∀ u ∈ U, y * u * y⁻¹ = u) (hV : ∀ v ∈ V, y * v * y⁻¹ ∈ V) :
    y ∈ Subgroup.normalizer ((U ⊔ V : Subgroup X) : Set X) := by
  have hle : U ⊔ V ≤ (U ⊔ V).comap (MulAut.conj y).toMonoidHom := by
    apply sup_le
    · intro u hu
      rw [Subgroup.mem_comap]
      show y * u * y⁻¹ ∈ U ⊔ V
      rw [hU u hu]
      exact Subgroup.mem_sup_left hu
    · intro v hv
      rw [Subgroup.mem_comap]
      show y * v * y⁻¹ ∈ U ⊔ V
      exact Subgroup.mem_sup_right (hV v hv)
  have hmap_le : (U ⊔ V).map (MulAut.conj y).toMonoidHom ≤ U ⊔ V := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_comap.mp (hle hz)
  have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
  have hcard : Nat.card (U ⊔ V : Subgroup X) ≤
      Nat.card ((U ⊔ V).map (MulAut.conj y).toMonoidHom) :=
    (Subgroup.card_map_of_injective hinj).ge
  have heq : (U ⊔ V).map (MulAut.conj y).toMonoidHom = U ⊔ V :=
    Subgroup.eq_of_le_of_card_ge hmap_le hcard
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
