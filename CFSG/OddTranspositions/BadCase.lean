module

public import CFSG.OddTranspositions.SecondKindCoset

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open scoped commutatorElement
open CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commutator_zpowers_eq_uv_of_inter_D_pair (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hbad : ∀ d : G, d ∈ (((Subgroup.zpowers u ⊔
        conjClosure (Subgroup.closure {u, w}) (u * v) : Subgroup G) : Set G) ∩ D) →
      d = u ∨ d = v) :
    (∀ x : G, x ∈ ⁅conjClosure (Subgroup.closure {u, w}) (u * v),
        Subgroup.zpowers u⁆ ↔ x = 1 ∨ x = u * v) ∧
    (∀ x : G, x ∈ ⁅conjClosure (Subgroup.closure {u, w}) (u * v),
        Subgroup.zpowers v⁆ ↔ x = 1 ∨ x = u * v) := by
  classical
  let Q : Subgroup G := conjClosure (Subgroup.closure ({u, w} : Set G)) (u * v)
  let S : Subgroup G := Subgroup.zpowers u ⊔ Q
  have hS : SecondKindStructure u w v := secondKind_structure hD hN htri h4 hno
  have hu2 : u * u = 1 := hD.mul_self_eq_one htri.1
  have hv2 : v * v = 1 := hD.mul_self_eq_one htri.2.1
  have huvc : Commute u v := htri.2.2.2.2.1
  have huv2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huvc.eq]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]
  have pair : ∀ {t : G}, t * t = 1 → ∀ z : G,
      (z ∈ Subgroup.zpowers t ↔ z = 1 ∨ z = t) := by
    intro t ht z
    constructor
    · intro hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
      · left
        rw [hm, zpow_mul, zpow_two, ht, one_zpow]
      · right
        rw [hm, zpow_add, zpow_mul, zpow_two, ht, one_zpow, one_mul, zpow_one]
    · rintro (hz1 | hzt)
      · rw [hz1]
        exact Subgroup.one_mem _
      · rw [hzt]
        exact Subgroup.mem_zpowers t
  obtain ⟨x, hx, hxu⟩ := hS.conj
  have hxQ : x ∈ Q := by
    change x ∈ conjClosure (Subgroup.closure ({u, w} : Set G)) (u * v)
    exact secondKind_commutator_zpowers_le hD hN htri h4 hno hx
  have hx2 : x * x = 1 := hS.sq x hxQ
  have huK : u ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hvK : v ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hQu : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := fun q hq => hS.normal u huK q hq
  have hQv : ∀ q ∈ Q, v * q * v⁻¹ ∈ Q := fun q hq => hS.normal v hvK q hq
  have huS : u ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have huvQ : u * v ∈ Q := by
    change u * v ∈ conjClosure (Subgroup.closure ({u, w} : Set G)) (u * v)
    exact Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by simp⟩
  have hvS : v ∈ S := by
    rw [← hxu]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hxQ) huS)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hxQ))
  have forward : ∀ c : G, (c = u ∨ c = v) → c * c = 1 → c ∈ D → c ∈ S →
      (∀ q ∈ Q, c * q * c⁻¹ ∈ Q) →
      ⁅Q, Subgroup.zpowers c⁆ ≤ Subgroup.zpowers (u * v) := by
    intro c hc hc2 hcD hcS hcQ
    rw [Subgroup.commutator_le]
    intro q hq z hz
    rcases (pair hc2 z).mp hz with hz1 | hzc
    · rw [hz1, commutatorElement_def]
      simp
    subst z
    have hq2 : q * q = 1 := hS.sq q hq
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    have htD : c * ⁅c, q⁆ ∈ D := by
      rw [← conj_eq_mul_commutator hc2 hq2]
      exact hN q c hcD
    have hcqQ : ⁅c, q⁆ ∈ Q := by
      have h1 : c * q * c⁻¹ ∈ Q := hcQ q hq
      have h2 : q⁻¹ ∈ Q := Subgroup.inv_mem _ hq
      have h3 := Subgroup.mul_mem _ h1 h2
      simpa [commutatorElement_def] using h3
    have htS : c * ⁅c, q⁆ ∈ S :=
      Subgroup.mul_mem _ hcS (Subgroup.mem_sup_right hcqQ)
    have ht := hbad (c * ⁅c, q⁆) ⟨htS, htD⟩
    have hqc : ⁅q, c⁆ = (c * ⁅c, q⁆) * c := by
      rw [commutatorElement_def, hcinv, ← conj_eq_mul_commutator hc2 hq2]
    have hfinal : ⁅q, c⁆ = 1 ∨ ⁅q, c⁆ = u * v := by
      rw [hqc]
      rcases hc with rfl | rfl <;> rcases ht with ht | ht
      · left; rw [ht, hu2]
      · right; rw [ht]; exact huvc.eq.symm
      · right; rw [ht]
      · left; rw [ht, hv2]
    exact (pair huv2 ⁅q, c⁆).mpr hfinal
  have huv_mem_u : u * v ∈ ⁅Q, Subgroup.zpowers u⁆ := by
    have hveq : v = u * ⁅u, x⁆ := by
      rw [← hxu]
      exact conj_eq_mul_commutator hu2 hx2
    have huv_eq : u * v = ⁅u, x⁆ := by
      rw [hveq]
      calc u * (u * ⁅u, x⁆) = (u * u) * ⁅u, x⁆ := by group
        _ = ⁅u, x⁆ := by rw [hu2, one_mul]
    rw [huv_eq, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hxQ
  have huv_mem_v : u * v ∈ ⁅Q, Subgroup.zpowers v⁆ := by
    have hxinv2 : x⁻¹ * x⁻¹ = 1 := by
      rw [← mul_inv_rev, hx2, inv_one]
    have hconj : x⁻¹ * v * x = v * ⁅v, x⁻¹⁆ := by
      simpa using conj_eq_mul_commutator hv2 hxinv2
    have hxinvx : x⁻¹ * v * x = u := by
      rw [← hxu]
      group
    have hu_eq : u = v * ⁅v, x⁻¹⁆ := by
      rw [← hxinvx, hconj]
    have huv_eq : u * v = ⁅v, x⁻¹⁆ := by
      calc u * v = v * u := huvc.eq
        _ = v * (v * ⁅v, x⁻¹⁆) := by rw [hu_eq]
        _ = (v * v) * ⁅v, x⁻¹⁆ := by group
        _ = ⁅v, x⁻¹⁆ := by rw [hv2, one_mul]
    rw [huv_eq, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers v)
      (Subgroup.inv_mem _ hxQ)
  have hu_le : ⁅Q, Subgroup.zpowers u⁆ ≤ Subgroup.zpowers (u * v) :=
    forward u (Or.inl rfl) hu2 htri.1 huS hQu
  have hv_le : ⁅Q, Subgroup.zpowers v⁆ ≤ Subgroup.zpowers (u * v) :=
    forward v (Or.inr rfl) hv2 htri.2.1 hvS hQv
  have hu_eq : ⁅Q, Subgroup.zpowers u⁆ = Subgroup.zpowers (u * v) :=
    le_antisymm hu_le (Subgroup.zpowers_le.mpr huv_mem_u)
  have hv_eq : ⁅Q, Subgroup.zpowers v⁆ = Subgroup.zpowers (u * v) :=
    le_antisymm hv_le (Subgroup.zpowers_le.mpr huv_mem_v)
  constructor
  · intro z
    change z ∈ ⁅Q, Subgroup.zpowers u⁆ ↔ z = 1 ∨ z = u * v
    rw [hu_eq]
    exact pair huv2 z
  · intro z
    change z ∈ ⁅Q, Subgroup.zpowers v⁆ ↔ z = 1 ∨ z = u * v
    rw [hv_eq]
    exact pair huv2 z

end CFSG.OddTranspositions
