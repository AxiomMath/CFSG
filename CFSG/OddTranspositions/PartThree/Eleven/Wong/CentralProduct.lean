module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentData
public import Mathlib.GroupTheory.NoncommCoprod
import CFSG.RankThree.PartTwo.Sec21.Hering233iSL2

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

theorem sl5_eq_one_or_neg_one_of_mul_self {x : SL5} (hx : x * x = 1) : x = 1 ∨ x = -1 := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact CFSG.RankThree.PartTwo.Sec21.Hering233i.sl2_eq_one_or_neg_one_of_mul_self h2 hx

theorem sl5_inv_neg_one : (-1 : SL5)⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, one_mul])

theorem sl5_neg_one_ne_one : (-1 : SL5) ≠ 1 := by decide

section CentralProduct

variable {G : Type*} [Group G] {t : G}

theorem mem_zpowers_of_orderOf_eq_two (ht : orderOf t = 2) {g : G} :
    g ∈ zpowers t ↔ g = 1 ∨ g = t := by
  refine ⟨fun hg => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    rw [← zpow_mod_orderOf, ht]
    have h0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h2 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
    rcases (by omega : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1) with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem eq_apply_neg_one {i : SL5 →* G} (hinj : Function.Injective i) (ht : orderOf t = 2)
    (hti : t ∈ i.range) : t = i (-1) := by
  obtain ⟨x, rfl⟩ := hti
  have h2 := pow_orderOf_eq_one (i x)
  rw [ht, pow_two, ← map_mul] at h2
  have hx : x * x = 1 := hinj (by rw [h2, map_one])
  rcases sl5_eq_one_or_neg_one_of_mul_self hx with rfl | rfl
  · rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · rfl

variable {i1 i2 : SL5 →* G} (inj1 : Function.Injective i1) (inj2 : Function.Injective i2)
  (ht : orderOf t = 2) (hcomm : ∀ x y : SL5, Commute (i1 x) (i2 y))
  (hmeet : i1.range ⊓ i2.range = zpowers t)
include inj1 ht hmeet

theorem eq_i1_neg_one : t = i1 (-1) :=
  eq_apply_neg_one inj1 ht (inf_le_left (a := i1.range) (b := i2.range) (hmeet ▸ mem_zpowers t))

omit inj1 in
include inj2 in
theorem eq_i2_neg_one : t = i2 (-1) :=
  eq_apply_neg_one inj2 ht (inf_le_right (a := i1.range) (b := i2.range) (hmeet ▸ mem_zpowers t))

include inj2 in
theorem i1_eq_i2_iff {x y : SL5} : i1 x = i2 y ↔ (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by
  constructor
  · intro h
    have hmem : i1 x ∈ zpowers t := hmeet ▸ mem_inf.mpr ⟨⟨x, rfl⟩, ⟨y, h.symm⟩⟩
    rcases (mem_zpowers_of_orderOf_eq_two ht).mp hmem with h1 | h1
    · have hx : x = 1 := inj1 (by rw [h1, map_one])
      have hy : y = 1 := inj2 (by rw [← h, h1, map_one])
      exact Or.inl ⟨hx, hy⟩
    · have hx : x = -1 := inj1 (by rw [h1, ← eq_i1_neg_one inj1 ht hmeet])
      have hy : y = -1 := inj2 (by rw [← h, h1, ← eq_i2_neg_one inj2 ht hmeet])
      exact Or.inr ⟨hx, hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [map_one, map_one]
    · rw [← eq_i1_neg_one inj1 ht hmeet, ← eq_i2_neg_one inj2 ht hmeet]

omit ht hmeet inj1 in
@[expose] def prodHom (hcomm : ∀ x y : SL5, Commute (i1 x) (i2 y)) : SL5 × SL5 →* G :=
  MonoidHom.noncommCoprod i1 i2 hcomm

omit ht hmeet inj1 in
theorem prodHom_apply (p : SL5 × SL5) : prodHom hcomm p = i1 p.1 * i2 p.2 := rfl

omit ht hmeet inj1 in
theorem range_prodHom : (prodHom hcomm).range = i1.range ⊔ i2.range :=
  MonoidHom.noncommCoprod_range i1 i2 hcomm

omit ht hmeet inj1 in
include hcomm in
theorem mem_sup_iff {g : G} : g ∈ i1.range ⊔ i2.range ↔ ∃ x y : SL5, i1 x * i2 y = g := by
  rw [← range_prodHom hcomm]
  exact ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩, fun ⟨x, y, h⟩ => ⟨(x, y), h⟩⟩

include inj2 in
theorem prodHom_eq_one_iff {x y : SL5} :
    i1 x * i2 y = 1 ↔ (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by
  rw [mul_eq_one_iff_eq_inv, ← map_inv, i1_eq_i2_iff inj1 inj2 ht hmeet, inv_eq_one,
    inv_eq_iff_eq_inv, sl5_inv_neg_one]

include inj2 hcomm in
theorem prodHom_eq_iff {x y x' y' : SL5} :
    i1 x * i2 y = i1 x' * i2 y' ↔ (x' = x ∧ y' = y) ∨ (x' = -x ∧ y' = -y) := by
  have e : ∀ a b : SL5, i1 a * i2 b = prodHom hcomm (a, b) := fun _ _ => rfl
  rw [e, e, ← inv_mul_eq_one, ← map_inv, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, prodHom_apply,
    prodHom_eq_one_iff inj1 inj2 ht hmeet]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨(inv_mul_eq_one.mp h1).symm, (inv_mul_eq_one.mp h2).symm⟩
    · exact Or.inr ⟨by rw [← mul_neg_one, ← h1, mul_inv_cancel_left],
        by rw [← mul_neg_one, ← h2, mul_inv_cancel_left]⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by rw [h1, inv_mul_cancel], by rw [h2, inv_mul_cancel]⟩
    · exact Or.inr ⟨by rw [h1, ← mul_neg_one, inv_mul_cancel_left],
        by rw [h2, ← mul_neg_one, inv_mul_cancel_left]⟩

include inj2 in
theorem card_ker_prodHom : Nat.card (prodHom hcomm).ker = 2 := by
  have h : ((prodHom hcomm).ker : Set (SL5 × SL5)) = {(1, 1), (-1, -1)} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, prodHom_apply, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    exact prodHom_eq_one_iff inj1 inj2 ht hmeet
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair]
  intro he
  exact sl5_neg_one_ne_one (congrArg Prod.fst he).symm

include inj2 in
theorem diag_eq_one_iff {x : SL5} : i1 x * i2 x = 1 ↔ x = 1 ∨ x = -1 := by
  rw [prodHom_eq_one_iff inj1 inj2 ht hmeet]
  exact ⟨fun h => h.imp And.left And.left, fun h => h.imp (fun h => ⟨h, h⟩) fun h => ⟨h, h⟩⟩

end CentralProduct

end CFSG.OddTranspositions.PartThree.Wong
