module

public import CFSG.GH74.Generic.S45.AutE8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Y : Type} [Group Y] [Finite Y]

theorem s16c167_seven_fix_eq_one (hY : Nat.card Y = 8) {l : MulAut Y} (hl : l ^ 7 = 1)
    (hne : l ≠ 1) {y : Y} (hy : l y = y) : y = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact CFSG.GH74.Generic.S45.fix_seven_eight hY l (orderOf_eq_prime hl hne) y hy

theorem s16c167_seven_orbit (hY : Nat.card Y = 8) {l : MulAut Y} (hl : l ^ 7 = 1) (hne : l ≠ 1)
    {y z : Y} (hy : y ≠ 1) (hz : z ≠ 1) : ∃ i : ℕ, (l ^ i) y = z := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ho : orderOf l = 7 := orderOf_eq_prime hl hne
  obtain ⟨g, hg, hgy⟩ := CFSG.GH74.Generic.S45.exists_zpowers_apply_eq hY ho hy hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  refine ⟨(k % (7 : ℤ)).toNat, ?_⟩
  have hk : (0 : ℤ) ≤ k % 7 := Int.emod_nonneg k (by norm_num)
  rw [← hgy, ← zpow_natCast, Int.toNat_of_nonneg hk]
  have := zpow_mod_orderOf l k
  rw [ho] at this
  rw [show ((7 : ℕ) : ℤ) = 7 from rfl] at this
  rw [this]

theorem s16c167_seven_cyclic (hY : Nat.card Y = 8) {H : Subgroup (MulAut Y)}
    (hH : ∀ h ∈ H, h ^ 7 = 1) {l : MulAut Y} (hl : l ∈ H) (hne : l ≠ 1) {h : MulAut Y}
    (hh : h ∈ H) : ∃ a : ℕ, h = l ^ a := by
  haveI : Nontrivial Y := (Finite.one_lt_card_iff_nontrivial (α := Y)).1 (by omega)
  obtain ⟨y, hy⟩ : ∃ y : Y, y ≠ 1 := exists_ne 1
  have hhy : h y ≠ 1 := fun h1 => hy (h.injective (by rw [h1, map_one]))
  obtain ⟨i, hi⟩ := s16c167_seven_orbit hY (hH l hl) hne hy hhy
  have hkH : (l ^ i)⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (H.pow_mem hl i)) hh
  have hk : ((l ^ i)⁻¹ * h) y = y := by
    rw [MulAut.mul_apply, ← hi]
    exact MulAut.inv_apply_self _ _ _
  by_cases hk1 : (l ^ i)⁻¹ * h = 1
  · exact ⟨i, (inv_mul_eq_one.1 hk1).symm⟩
  · exact absurd (s16c167_seven_fix_eq_one hY (hH _ hkH) hk1 hk) hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
