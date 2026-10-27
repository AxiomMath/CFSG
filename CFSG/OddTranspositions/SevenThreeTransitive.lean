module

public import CFSG.OddTranspositions.SevenThreeKind

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def LocalSecond (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ x y t : G, Commute x d → Commute y d → Commute t d →
    IsTriangle D x y t → orderOf (x * t * y) = 4

def thirdOrbit (D : Set G) (z u : G) : Set G :=
  {x | ∃ k ∈ thirdK D z, k * u * k⁻¹ = x}

theorem mem_thirdOrbit_self {z u : G} (hu : u ∈ Delta D z) : u ∈ thirdOrbit D z u :=
  ⟨1, one_mem _, by simp⟩

theorem thirdOrbit_subset_Delta (hN : IsNormalSet D) {z u : G} (hu : u ∈ Delta D z) :
    thirdOrbit D z u ⊆ Delta D z := by
  rintro x ⟨k, hk, rfl⟩
  have hkz : Commute k z :=
    (Subgroup.mem_centralizer_iff.mp (thirdK_le_centralizer hk) z (by simp)).symm
  have huz : Commute u z := (mem_Delta_iff.mp hu).2
  refine mem_Delta_iff.mpr ⟨hN k u (mem_Delta_iff.mp hu).1, ?_⟩
  exact ((hkz.symm.mul_right huz.symm).mul_right hkz.symm.inv_right).symm

theorem thirdOrbit_invariant {z u : G} :
    ∀ k' ∈ thirdK D z, ∀ x ∈ thirdOrbit D z u, k' * x * k'⁻¹ ∈ thirdOrbit D z u := by
  rintro k' hk' x ⟨k, hk, rfl⟩
  refine ⟨k' * k, Subgroup.mul_mem _ hk' hk, ?_⟩
  group

theorem disjoint_thirdOrbit_of_not_mem {z u x : G} (hx : x ∉ thirdOrbit D z u) :
    Disjoint (thirdOrbit D z u) (thirdOrbit D z x) := by
  rw [Set.disjoint_left]
  rintro y ⟨k, hk, hky⟩ ⟨k', hk', hky'⟩
  apply hx
  refine ⟨k'⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hk') hk, ?_⟩
  calc (k'⁻¹ * k) * u * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * u * k⁻¹) * k' := by group
    _ = k'⁻¹ * y * k' := by rw [hky]
    _ = x := by
      rw [← hky']
      group

theorem thirdK_transitive (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) :
    ∀ x ∈ Delta D ((u * v * w) ^ n),
      ∃ k ∈ thirdK D ((u * v * w) ^ n), k * u * k⁻¹ = x := by
  classical
  let z : G := (u * v * w) ^ n
  let K : Subgroup G := thirdK D z
  have hthird := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  obtain ⟨hz2, hz1, hzu, hzv, hzw, hbD⟩ := hthird
  have huD : u ∈ D := htri.1
  have hvD : v ∈ D := htri.2.1
  have hwD : w ∈ D := htri.2.2.1
  have huΔ : u ∈ Delta D z := mem_Delta_iff.mpr ⟨huD, hzu.symm⟩
  have hvΔ : v ∈ Delta D z := mem_Delta_iff.mpr ⟨hvD, hzv.symm⟩
  have hwΔ : w ∈ Delta D z := mem_Delta_iff.mpr ⟨hwD, hzw.symm⟩
  have huw : ¬ Commute u w := htri.2.2.2.2.2.1
  have hvw : ¬ Commute v w := htri.2.2.2.2.2.2
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one huD
  have hv2 : v * v = 1 := hS.oddT.mul_self_eq_one hvD
  have hw2 : w * w = 1 := hS.oddT.mul_self_eq_one hwD
  have hodduw : Odd (orderOf (u * w)) := hS.oddT.odd_of_not_commute huD hwD huw
  have hoddvw : Odd (orderOf (v * w)) := hS.oddT.odd_of_not_commute hvD hwD hvw
  obtain ⟨gu, hgu, hguw⟩ := exists_conj_of_odd_orderOf_mul hu2 hw2 hodduw
  have huwK : Subgroup.closure ({u, w} : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact Delta_subset_thirdK huΔ
    · exact Delta_subset_thirdK hwΔ
  have hwO : w ∈ thirdOrbit D z u := ⟨gu, huwK hgu, hguw⟩
  obtain ⟨gv, hgv, hgvw⟩ := exists_conj_of_odd_orderOf_mul hv2 hw2 hoddvw
  have hvwK : Subgroup.closure ({v, w} : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact Delta_subset_thirdK hvΔ
    · exact Delta_subset_thirdK hwΔ
  have hgvK : gv ∈ K := hvwK hgv
  have hvO : v ∈ thirdOrbit D z u := by
    refine ⟨gv⁻¹ * gu, Subgroup.mul_mem _ (Subgroup.inv_mem _ hgvK) (huwK hgu), ?_⟩
    calc (gv⁻¹ * gu) * u * (gv⁻¹ * gu)⁻¹ = gv⁻¹ * (gu * u * gu⁻¹) * gv := by group
      _ = gv⁻¹ * w * gv := by rw [hguw]
      _ = v := by
        rw [← hgvw]
        group
  intro x hx
  by_cases hxO : x ∈ thirdOrbit D z u
  · obtain ⟨k, hk, hkx⟩ := hxO
    exact ⟨k, hk, hkx⟩
  · exfalso
    have hΔu : thirdOrbit D z u ⊆ Delta D z := thirdOrbit_subset_Delta hS.normal huΔ
    have hΔx : thirdOrbit D z x ⊆ Delta D z := thirdOrbit_subset_Delta hS.normal hx
    have hdisj : Disjoint (thirdOrbit D z u) (thirdOrbit D z x) :=
      disjoint_thirdOrbit_of_not_mem hxO
    have hcomm := thirdK_orbits_commute hS hΔu hΔx
      (thirdOrbit_invariant (z := z) (u := u))
      (thirdOrbit_invariant (z := z) (u := x)) hdisj
    have hxu : Commute u x := hcomm u (mem_thirdOrbit_self huΔ) x (mem_thirdOrbit_self hx)
    have hxv : Commute v x := hcomm v hvO x (mem_thirdOrbit_self hx)
    have hxw : Commute w x := hcomm w hwO x (mem_thirdOrbit_self hx)
    have hsec := hL x (mem_Delta_iff.mp hx).1 u w v hxu hxw hxv htri
    rw [hord] at hsec
    obtain ⟨k, hk⟩ := hn
    rw [hk] at hsec
    omega

theorem thirdInv_not_mem (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) :
    (u * v * w) ^ n ∉ D := by
  classical
  intro hzD
  let z : G := (u * v * w) ^ n
  have hthird := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  obtain ⟨hz2, hz1, hzu, hzv, hzw, hbD⟩ := hthird
  have hzΔ : z ∈ Delta D z := mem_Delta_iff.mpr ⟨hzD, Commute.refl z⟩
  obtain ⟨k, hk, hku⟩ := thirdK_transitive hS hL htri hn hord z hzΔ
  have hkz : Commute k z := by
    have h := Subgroup.mem_centralizer_iff.mp (thirdK_le_centralizer hk)
    exact (h z (Set.mem_singleton z)).symm
  have hu_eq_z : u = z := by
    calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
      _ = k⁻¹ * z * k := by rw [hku]
      _ = z := by
        rw [hkz.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have huw : Commute u w := by
    rw [hu_eq_z]
    exact hzw
  exact htri.2.2.2.2.2.1 huw

end CFSG.OddTranspositions
