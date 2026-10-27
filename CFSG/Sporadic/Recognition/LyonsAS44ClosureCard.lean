module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

private theorem disjoint_zpowers_of_pow_three_aux {G : Type*} [Group G] {B : Subgroup G} {z : G}
    (hz3 : z ^ 3 = 1) (hzB : z ∉ B) : Disjoint B (Subgroup.zpowers z) := by
  have hz1 : z ≠ 1 := fun h => hzB (h ▸ B.one_mem)
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hz3' : z * z * z = 1 := by rwa [pow_succ, pow_two] at hz3
  rw [Subgroup.disjoint_def]
  intro x hxB hxz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have hk : z ^ k = z ^ (k % 3) := by
    have h := zpow_mod_orderOf z k
    rw [hord] at h
    simpa using h.symm
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hk] at hxB ⊢
  rcases hmod with h | h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hxB
    exact absurd hxB hzB
  · rw [h, zpow_two] at hxB
    refine absurd ?_ hzB
    have hsq : z * z * (z * z) = z := by
      calc z * z * (z * z) = (z * z * z) * z := by simp only [mul_assoc]
        _ = z := by rw [hz3', one_mul]
    exact hsq ▸ B.mul_mem hxB hxB

theorem card_closure_union_singleton_eq_three_mul {G : Type*} [Group G] [Finite G]
    {B : Subgroup G} {z : G} (hz3 : z ^ 3 = 1) (hzB : z ∉ B)
    (hcomm : ∀ b ∈ B, b * z = z * b) :
    Nat.card ↥(Subgroup.closure ((B : Set G) ∪ {z})) = 3 * Nat.card ↥B := by
  have hz1 : z ≠ 1 := fun h => hzB (h ▸ B.one_mem)
  have hcard : Nat.card (Subgroup.zpowers z) = 3 := by
    have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hz3⟩
    rw [← Nat.card_congr (finEquivZPowers hfin), Nat.card_eq_fintype_card, Fintype.card_fin,
      orderOf_eq_prime hz3 hz1]
  have hcomm' : ∀ (b : B) (c : Subgroup.zpowers z),
      Commute (B.subtype b) ((Subgroup.zpowers z).subtype c) := by
    intro b c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.2
    rw [Subgroup.coe_subtype, Subgroup.coe_subtype, ← hk]
    exact (show Commute (b : G) z from hcomm b b.2).zpow_right k
  have hinj : Function.Injective (MonoidHom.noncommCoprod B.subtype
      (Subgroup.zpowers z).subtype hcomm') := by
    rw [MonoidHom.noncommCoprod_injective, Subgroup.range_subtype, Subgroup.range_subtype]
    exact ⟨B.subtype_injective, (Subgroup.zpowers z).subtype_injective,
      disjoint_zpowers_of_pow_three_aux hz3 hzB⟩
  have hrange : (MonoidHom.noncommCoprod B.subtype (Subgroup.zpowers z).subtype hcomm').range =
      Subgroup.closure ((B : Set G) ∪ {z}) := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype,
      Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  calc Nat.card ↥(Subgroup.closure ((B : Set G) ∪ {z}))
      = Nat.card ↥(MonoidHom.noncommCoprod B.subtype (Subgroup.zpowers z).subtype hcomm').range :=
        by rw [hrange]
    _ = Nat.card (B × Subgroup.zpowers z) :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    _ = Nat.card B * Nat.card (Subgroup.zpowers z) := Nat.card_prod _ _
    _ = 3 * Nat.card ↥B := by rw [hcard, mul_comm]

theorem card_closure_conj_image {G : Type*} [Group G] (Z : Set G) (g : G) :
    Nat.card ↥(Subgroup.closure ((fun x => g * x * g⁻¹) '' Z)) =
      Nat.card ↥(Subgroup.closure Z) := by
  have h : Subgroup.closure ((fun x => g * x * g⁻¹) '' Z) =
      (Subgroup.closure Z).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure]
    rfl
  rw [h]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem closure_le_closure_of_mem_or_inv {G : Type*} [Group G] {Z Z' : Set G}
    (h : ∀ z ∈ Z, ∃ z' ∈ Z', z = z' ∨ z = z'⁻¹) :
    Subgroup.closure Z ≤ Subgroup.closure Z' := by
  rw [Subgroup.closure_le]
  intro z hz
  obtain ⟨z', hz', rfl | rfl⟩ := h z hz
  · exact Subgroup.subset_closure hz'
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure hz')

theorem closure_eq_closure_of_mem_or_inv {G : Type*} [Group G] {Z Z' : Set G}
    (h1 : ∀ z ∈ Z, ∃ z' ∈ Z', z = z' ∨ z = z'⁻¹) (h2 : ∀ z' ∈ Z', ∃ z ∈ Z, z' = z ∨ z' = z⁻¹) :
    Subgroup.closure Z = Subgroup.closure Z' :=
  le_antisymm (closure_le_closure_of_mem_or_inv h1) (closure_le_closure_of_mem_or_inv h2)

end CFSG.Sporadic.Recognition.LyonsSims
