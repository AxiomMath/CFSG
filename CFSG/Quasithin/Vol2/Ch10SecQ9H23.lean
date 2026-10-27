module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.Quasithin.Vol2.Ch10SecQ9H16
public import CFSG.Quasithin.Vol2.Ch10SecQ9H17
public import CFSG.Quasithin.Vol2.Ch10SecQ9H20

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

theorem eq_one_of_center_section {X : Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2))}
    (hX : X ≤ stabStd m k) (f : ↥(stabStd m k) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (himg : (X.subgroupOf (stabStd m k)).map f = ⊤) {y : ↥(stabStd m k)}
    (hyc : ∀ x ∈ X, y.1 * x * y.1⁻¹ * x⁻¹ ∈ o2G X) : f y = 1 := by
  set N := ((o2G X).subgroupOf (stabStd m k)).map f with hN
  have hsurj : ∀ s, ∃ x : ↥(stabStd m k), x.1 ∈ X ∧ f x = s := fun s => by
    have hs : s ∈ (X.subgroupOf (stabStd m k)).map f := by rw [himg]; trivial
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hNn : N.Normal := ⟨fun n hn g => by
    obtain ⟨q, hq, rfl⟩ := hn
    obtain ⟨x, hx, rfl⟩ := hsurj g
    refine ⟨x * q * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_o2G X hx) _).mp
      (Subgroup.mem_subgroupOf.mp hq)⟩
  have hNp : IsPGroup 2 N := by
    refine IsPGroup.map ?_ f
    exact (isPGroup_o2G X).of_equiv (Subgroup.subgroupOfEquivOfLe ((o2G_le X).trans hX)).symm
  have hN1 := eq_bot_of_normal_two (by norm_num) hNn hNp
  have hc : ∀ s, f y * s = s * f y := fun s => by
    obtain ⟨x, hx, rfl⟩ := hsurj s
    have h1 : f (y * x * y⁻¹ * x⁻¹) ∈ N := ⟨y * x * y⁻¹ * x⁻¹,
      Subgroup.mem_subgroupOf.mpr (hyc x.1 hx), rfl⟩
    rw [hN1, Subgroup.mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc f y * f x = f y * f x * (f y)⁻¹ * (f x)⁻¹ * (f x * f y) := by group
      _ = f x * f y := by rw [h1, one_mul]
  have hcen : f y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Subgroup.mem_center_iff.mpr fun s => (hc s).symm
  rw [center_SL_eq_bot 3, Subgroup.mem_bot] at hcen
  exact hcen

theorem blocks_ne_of_orderOf_three {y : ↥(stabStd m k)} (hy : orderOf y.1 = 3)
    (ht : topH m k y = 1) (hb : botH m k y = 1) : False := by
  have h2 := sq_eq_one_of_blocks y.2 (congrArg Subtype.val ht) (congrArg Subtype.val hb)
  have h3 : y.1 ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one _
  have h1 : y.1 = 1 := by
    calc y.1 = y.1 ^ 3 * (y.1 * y.1)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  rw [h1, orderOf_one] at hy
  omega

theorem sq_conj_of_blocks {y r : ↥(stabStd m k)}
    (ht : topH m k (r * y * r⁻¹ * y) = 1) (hb : botH m k (r * y * r⁻¹ * y) = 1) :
    (r.1 * y.1 * r.1⁻¹ * y.1) ^ 2 ^ 1 = 1 := by
  rw [pow_one, pow_two]
  exact sq_eq_one_of_blocks (r * y * r⁻¹ * y).2 (congrArg Subtype.val ht) (congrArg Subtype.val hb)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
