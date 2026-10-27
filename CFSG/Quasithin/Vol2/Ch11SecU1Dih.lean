module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open DihedralGroup

theorem dihedral_mem_zpowers_r_one {n : ℕ} [NeZero n] {x : DihedralGroup n}
    (hx : Odd (orderOf x)) : x ∈ Subgroup.zpowers (r 1 : DihedralGroup n) := by
  rcases x with i | i
  · refine Subgroup.mem_zpowers_iff.mpr ⟨(i.cast : ℤ), ?_⟩
    rw [r_one_zpow, ZMod.intCast_zmod_cast]
  · rw [orderOf_sr] at hx
    exact absurd hx (by decide)

theorem dihedral_le_zpowers_r_one {n : ℕ} [NeZero n] {P : Subgroup (DihedralGroup n)}
    (hP : Odd (Nat.card P)) : P ≤ Subgroup.zpowers (r 1 : DihedralGroup n) := fun _ hx =>
  dihedral_mem_zpowers_r_one (Odd.of_dvd_nat hP (Subgroup.orderOf_dvd_natCard P hx))

theorem dihedral_eq_of_odd {n : ℕ} [NeZero n] {P Q : Subgroup (DihedralGroup n)}
    (hP : Odd (Nat.card P)) (hPQ : Nat.card P = Nat.card Q) : P = Q := by
  set R := Subgroup.zpowers (r 1 : DihedralGroup n)
  have hPR := dihedral_le_zpowers_r_one hP
  have hQR := dihedral_le_zpowers_r_one (hPQ ▸ hP)
  have h1 : P.subgroupOf R = Q.subgroupOf R := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv, hPQ]
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hPR, inf_eq_left.mpr hQR] at h1
  exact h1

theorem dihedral_not_centralizes {n : ℕ} [NeZero n] (hn : Odd n) {P : Subgroup (DihedralGroup n)}
    (hP : Odd (Nat.card P)) (hP1 : P ≠ ⊥) {y : DihedralGroup n} (hy : orderOf y = 2) :
    ∃ x ∈ P, y * x ≠ x * y := by
  obtain ⟨x, hxP, hx1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hP1
  have hxo : Odd (orderOf x) := Odd.of_dvd_nat hP (Subgroup.orderOf_dvd_natCard P hxP)
  refine ⟨x, hxP, fun hc => hx1 ?_⟩
  have h2 : IsUnit (2 : ZMod n) := by
    simpa using (ZMod.unitOfCoprime 2 ((Nat.coprime_two_left).mpr hn)).isUnit
  rcases y with i | i
  ·
    have hpow : (r i : DihedralGroup n) ^ n = 1 := by
      rw [r_pow, ZMod.natCast_self, mul_zero, one_def]
    have := Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one hpow)
    rw [hy] at this
    exact absurd this (by decide)
  · rcases x with j | j
    · rw [sr_mul_r, r_mul_sr, sr.injEq] at hc
      have hjj : j = -j := add_left_cancel (hc.trans (sub_eq_add_neg i j))
      have hj : 2 * j = 0 := by
        rw [two_mul]
        nth_rewrite 1 [hjj]
        exact neg_add_cancel j
      rw [(h2.mul_right_eq_zero).mp hj, one_def]
    · rw [orderOf_sr] at hxo
      exact absurd hxo (by decide)

theorem eq_of_odd_of_mulEquiv {X : Type*} [Group X] {n : ℕ} [NeZero n] (d : X ≃* DihedralGroup n)
    {P Q : Subgroup X} (hP : Odd (Nat.card P)) (hPQ : Nat.card P = Nat.card Q) : P = Q := by
  have hcard : ∀ S : Subgroup X, Nat.card (S.map d.toMonoidHom) = Nat.card S := fun S =>
    Subgroup.card_map_of_injective d.injective
  have h := dihedral_eq_of_odd (P := P.map d.toMonoidHom) (Q := Q.map d.toMonoidHom)
    (by rw [hcard]; exact hP) (by rw [hcard, hcard, hPQ])
  exact Subgroup.map_injective d.injective h

theorem not_centralizes_of_mulEquiv {X : Type*} [Group X] {n : ℕ} [NeZero n] (hn : Odd n)
    (d : X ≃* DihedralGroup n) {P : Subgroup X} (hP : Odd (Nat.card P)) (hP1 : P ≠ ⊥) {y : X}
    (hy : orderOf y = 2) : ∃ x ∈ P, y * x ≠ x * y := by
  obtain ⟨x', hx', hc⟩ := dihedral_not_centralizes hn (P := P.map d.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective d.injective]; exact hP)
    (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ d.injective])
    (y := d y) (by rw [MulEquiv.orderOf_eq]; exact hy)
  obtain ⟨x, hx, rfl⟩ := hx'
  refine ⟨x, hx, fun h => hc ?_⟩
  change d y * d x = d x * d y
  rw [← map_mul, ← map_mul, h]

end CFSG.Quasithin.Vol2.Ch11.SecU1
