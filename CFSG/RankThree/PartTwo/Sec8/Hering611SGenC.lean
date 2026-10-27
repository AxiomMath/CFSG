module

public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {G : Type} [Group G]

theorem conj_eq_zpow_of_transvections {a d w u : G} (had : a * d = d * a) {ε δ : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (hw1 : w⁻¹ * a * w = a * d ^ ε) (hw2 : w⁻¹ * d * w = d)
    (hu1 : u⁻¹ * a * u = a) (hu2 : u⁻¹ * d * u = d * a ^ δ) :
    (w * u ^ (-(ε * δ)))⁻¹ * a * (w * u ^ (-(ε * δ))) = d ^ ε := by
  have hau : a * u = u * a := by
    calc a * u = u * (u⁻¹ * a * u) := by group
      _ = u * a := by rw [hu1]
  have hua : u * a * u⁻¹ = a := by
    rw [← hau]
    group
  have hu1' : u⁻¹ * a⁻¹ * u = a⁻¹ := by
    calc u⁻¹ * a⁻¹ * u = (u⁻¹ * a * u)⁻¹ := by group
      _ = a⁻¹ := by rw [hu1]
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
  ·
    have hud : u * d * u⁻¹ = d * a⁻¹ := by
      have h1 : u * d * u⁻¹ * a = d := by
        calc u * d * u⁻¹ * a = u * d * (u⁻¹ * a * u) * u⁻¹ := by group
          _ = u * d * a * u⁻¹ := by rw [hu1]
          _ = u * (d * a) * u⁻¹ := by group
          _ = u * (u⁻¹ * d * u) * u⁻¹ := by rw [hu2, zpow_one]
          _ = d := by group
      calc u * d * u⁻¹ = u * d * u⁻¹ * a * a⁻¹ := by group
        _ = d * a⁻¹ := by rw [h1]
    rw [show -(1 * 1 : ℤ) = -1 by norm_num, zpow_neg_one, zpow_one]
    calc (w * u⁻¹)⁻¹ * a * (w * u⁻¹) = u * (w⁻¹ * a * w) * u⁻¹ := by group
      _ = u * (a * d) * u⁻¹ := by rw [hw1, zpow_one]
      _ = (u * a * u⁻¹) * (u * d * u⁻¹) := by group
      _ = a * (d * a⁻¹) := by rw [hua, hud]
      _ = (a * d) * a⁻¹ := by group
      _ = (d * a) * a⁻¹ := by rw [had]
      _ = d := by group
  ·
    rw [show -(1 * -1 : ℤ) = 1 by norm_num, zpow_one, zpow_one]
    calc (w * u)⁻¹ * a * (w * u) = u⁻¹ * (w⁻¹ * a * w) * u := by group
      _ = u⁻¹ * (a * d) * u := by rw [hw1, zpow_one]
      _ = (u⁻¹ * a * u) * (u⁻¹ * d * u) := by group
      _ = a * (d * a⁻¹) := by rw [hu1, hu2, zpow_neg_one]
      _ = (a * d) * a⁻¹ := by group
      _ = (d * a) * a⁻¹ := by rw [had]
      _ = d := by group
  ·
    rw [show -(-1 * 1 : ℤ) = 1 by norm_num, zpow_one, zpow_neg_one]
    calc (w * u)⁻¹ * a * (w * u) = u⁻¹ * (w⁻¹ * a * w) * u := by group
      _ = u⁻¹ * (a * d⁻¹) * u := by rw [hw1, zpow_neg_one]
      _ = (u⁻¹ * a * u) * (u⁻¹ * d * u)⁻¹ := by group
      _ = a * (d * a)⁻¹ := by rw [hu1, hu2, zpow_one]
      _ = a * (a⁻¹ * d⁻¹) := by group
      _ = d⁻¹ := by group
  ·
    have hud : u * d * u⁻¹ = d * a := by
      have h1 : u * d * u⁻¹ * a⁻¹ = d := by
        calc u * d * u⁻¹ * a⁻¹ = u * d * (u⁻¹ * a⁻¹ * u) * u⁻¹ := by group
          _ = u * d * a⁻¹ * u⁻¹ := by rw [hu1']
          _ = u * (d * a⁻¹) * u⁻¹ := by group
          _ = u * (u⁻¹ * d * u) * u⁻¹ := by rw [hu2, zpow_neg_one]
          _ = d := by group
      calc u * d * u⁻¹ = u * d * u⁻¹ * a⁻¹ * a := by group
        _ = d * a := by rw [h1]
    rw [show -(-1 * -1 : ℤ) = -1 by norm_num, zpow_neg_one, zpow_neg_one]
    calc (w * u⁻¹)⁻¹ * a * (w * u⁻¹) = u * (w⁻¹ * a * w) * u⁻¹ := by group
      _ = u * (a * d⁻¹) * u⁻¹ := by rw [hw1, zpow_neg_one]
      _ = (u * a * u⁻¹) * (u * d * u⁻¹)⁻¹ := by group
      _ = a * (d * a)⁻¹ := by rw [hua, hud]
      _ = a * (a⁻¹ * d⁻¹) := by group
      _ = d⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec8.Hering611
