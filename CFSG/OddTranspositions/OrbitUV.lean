module

public import CFSG.OddTranspositions.RotationCommute

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem card_orbit_conj_uv (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v) :
    Nat.card {x : G | ∃ a ∈ Subgroup.closure ({u, w} : Set G), x = a * (u * v) * a⁻¹}
      = orderOf (u * w) := by
  have hu2 : u * u = 1 := hD.mul_self_eq_one htri.1
  have hw2 : w * w = 1 := hD.mul_self_eq_one htri.2.2.1
  have huc : Commute u (u * v) := (Commute.refl u).mul_right htri.2.2.2.2.1
  have huc' : u * (u * v) * u⁻¹ = u * v := by
    rw [huc.eq, mul_assoc, hD.inv_eq htri.1, hu2, mul_one]
  let A := Subgroup.closure ({u, w} : Set G)
  have huA : u ∈ A := Subgroup.subset_closure (by simp)
  have hwA : w ∈ A := Subgroup.subset_closure (by simp)
  have huwA : u * w ∈ A := A.mul_mem huA hwA
  let R := Subgroup.zpowers (u * w)
  have hRA : R ≤ A := Subgroup.zpowers_le.mpr huwA
  have hconj_reflect (r : G) :
      (r * u) * (u * v) * (r * u)⁻¹ = r * (u * v) * r⁻¹ := by
    calc (r * u) * (u * v) * (r * u)⁻¹
        = r * (u * (u * v) * u) * r⁻¹ := by
          rw [mul_inv_rev, hD.inv_eq htri.1]
          group
      _ = r * (u * (u * v) * u⁻¹) * r⁻¹ := by rw [hD.inv_eq htri.1]
      _ = r * (u * v) * r⁻¹ := by rw [huc']
  let f : R → {x : G | ∃ a ∈ A, x = a * (u * v) * a⁻¹} := fun r =>
    ⟨r.1 * (u * v) * r.1⁻¹, ⟨r.1, hRA r.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    ·
      intro r1 r2 h
      have hv : r1.1 * (u * v) * r1.1⁻¹ = r2.1 * (u * v) * r2.1⁻¹ := by
        simpa [f] using congrArg Subtype.val h
      have htR : r2.1⁻¹ * r1.1 ∈ R := R.mul_mem (R.inv_mem r2.2) r1.2
      have htconj : (r2.1⁻¹ * r1.1) * (u * v) * (r2.1⁻¹ * r1.1)⁻¹ = u * v := by
        rw [mul_inv_rev, inv_inv]
        calc r2.1⁻¹ * r1.1 * (u * v) * (r1.1⁻¹ * r2.1)
            = r2.1⁻¹ * (r1.1 * (u * v) * r1.1⁻¹) * r2.1 := by group
          _ = r2.1⁻¹ * (r2.1 * (u * v) * r2.1⁻¹) * r2.1 := by rw [hv]
          _ = u * v := by group
      have htcomm : Commute (r2.1⁻¹ * r1.1) (u * v) := by
        rw [commute_iff_eq]
        calc (r2.1⁻¹ * r1.1) * (u * v)
            = (r2.1⁻¹ * r1.1) * (u * v) * (r2.1⁻¹ * r1.1)⁻¹ * (r2.1⁻¹ * r1.1) := by
              group
          _ = (u * v) * (r2.1⁻¹ * r1.1) := by
              rw [htconj]
      by_cases h1 : r2.1⁻¹ * r1.1 = 1
      · exact Subtype.ext (inv_mul_eq_one.mp h1).symm
      · exact absurd htcomm (rotation_not_commute_uv hD hN htri h4 hno htR h1)
    ·
      rintro ⟨x, a, ha, rfl⟩
      obtain ⟨i, hi | hi⟩ := exists_zpow_of_mem_closure_pair hu2 hw2 ha
      · refine ⟨⟨(u * w) ^ i, Subgroup.zpow_mem_zpowers (u * w) i⟩, ?_⟩
        apply Subtype.ext
        simp only [f]
        rw [hi]
      · refine ⟨⟨(u * w) ^ i, Subgroup.zpow_mem_zpowers (u * w) i⟩, ?_⟩
        apply Subtype.ext
        simp only [f]
        rw [hi]
        exact (hconj_reflect ((u * w) ^ i)).symm
  calc Nat.card {x : G | ∃ a ∈ Subgroup.closure ({u, w} : Set G), x = a * (u * v) * a⁻¹}
      = Nat.card R := Nat.card_congr (Equiv.ofBijective f hf).symm
    _ = orderOf (u * w) := Nat.card_zpowers (u * w)

end CFSG.OddTranspositions
