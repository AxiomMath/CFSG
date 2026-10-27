module

public import CFSG.Timmesfeld.Transvection.CommMap
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Timmesfeld.Transvection

variable {G : Type*} [Group G] {M : Subgroup G} {h : G}
  (hM : ∀ x ∈ M, ∀ y ∈ M, Commute x y) (hhM : ∀ x ∈ M, h * x * h⁻¹ ∈ M)

theorem commute_of_commute_sq_of_odd {y : G} (hodd : Odd (orderOf h))
    (hy : Commute (h ^ 2) y) : Commute h y := by
  obtain ⟨k, hk⟩ := hodd
  have hpow : h = (h ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf h + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hpow]
  exact hy.pow_left _

include hM hhM

theorem inf_ker_range_commMap (h2 : ∀ x ∈ M, x * x = 1) (hodd : Odd (orderOf h)) :
    (commMap hM hhM).ker ⊓ (commMap hM hhM).range = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hck, y, rfl⟩
  have hck : Commute ((commMap hM hhM y : M) : G) h := (mem_ker_commMap_iff hM hhM _).1 hck
  have hyM := y.2
  have hαy : h * (y : G) * h⁻¹ ∈ M := hhM _ hyM
  have hyinv : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right (h2 _ hyM)
  have hc : ((commMap hM hhM y : M) : G) = y * (h * y * h⁻¹) := by
    rw [coe_commMap, hyinv]
    group
  have hαc : h * ((commMap hM hhM y : M) : G) * h⁻¹ = (commMap hM hhM y : M) := by
    rw [← hck.eq]
    group
  have hcomm : Commute (h * (y : G) * h⁻¹) y := hM _ hαy _ hyM
  have hb : h * (h * (y : G) * h⁻¹) * h⁻¹ = y := by
    have h1 := hαc
    rw [hc] at h1
    have h2' : h * ((y : G) * (h * y * h⁻¹)) * h⁻¹ =
        (h * (y : G) * h⁻¹) * (h * (h * y * h⁻¹) * h⁻¹) := by group
    rw [h2', hcomm.symm.eq] at h1
    exact mul_left_cancel h1
  have hsq : Commute (h ^ 2) (y : G) := by
    show h ^ 2 * y = y * h ^ 2
    rw [pow_two]
    calc h * h * (y : G) = h * (h * (y : G) * h⁻¹) * h⁻¹ * (h * h) := by group
      _ = y * (h * h) := by rw [hb]
  have hy1 := (commute_of_commute_sq_of_odd hodd hsq).eq
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hc, show h * (y : G) * h⁻¹ = y by rw [hy1, mul_inv_cancel_right], h2 _ hyM]
  rfl

theorem mul_injective_commMap (h2 : ∀ x ∈ M, x * x = 1) (hodd : Odd (orderOf h)) :
    Function.Injective fun p : (commMap hM hhM).ker × (commMap hM hhM).range =>
      (p.1 : M) * p.2 := by
  have hdisj := inf_ker_range_commMap hM hhM h2 hodd
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have h1 : (a : M) * b = a' * b' := hab
  have h3 : (a' : M)⁻¹ * a = b' * (b : M)⁻¹ := by
    calc (a' : M)⁻¹ * a = (a' : M)⁻¹ * (a * b) * (b : M)⁻¹ := by group
      _ = (a' : M)⁻¹ * (a' * b') * (b : M)⁻¹ := by rw [h1]
      _ = b' * (b : M)⁻¹ := by group
  have hmem : (a' : M)⁻¹ * a ∈ (commMap hM hhM).ker ⊓ (commMap hM hhM).range :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a'.2) a.2,
      h3 ▸ Subgroup.mul_mem _ b'.2 (Subgroup.inv_mem _ b.2)⟩
  rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hb : (b : M) = b' := by
    rw [hmem] at h1
    exact mul_left_cancel h1
  simp only [Prod.mk.injEq]
  exact ⟨Subtype.ext hmem.symm, Subtype.ext hb⟩

theorem exists_eq_mul_commMap [Finite G] (h2 : ∀ x ∈ M, x * x = 1) (hodd : Odd (orderOf h))
    (x : M) : ∃ c : M, Commute (c : G) h ∧ ∃ y : M, x = c * commMap hM hhM y := by
  have hinj := mul_injective_commMap hM hhM h2 hodd
  have hcard : Nat.card ((commMap hM hhM).ker × (commMap hM hhM).range) = Nat.card M := by
    rw [Nat.card_prod, mul_comm, card_range_commMap_mul hM hhM]
  have hsurj := (Function.Injective.bijective_of_nat_card_le hinj hcard.ge).2
  obtain ⟨⟨c, r⟩, hcr⟩ := hsurj x
  obtain ⟨y, hy⟩ := r.2
  refine ⟨c, (mem_ker_commMap_iff hM hhM c).1 c.2, y, ?_⟩
  rw [← hcr]
  simp only [hy]

end CFSG.Timmesfeld.Transvection
