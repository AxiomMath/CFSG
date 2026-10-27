module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

namespace FiveTransitive.InvolutiveNormalizerExtension

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

private theorem zpowers_cases (b : G) (hb : orderOf b = 2) {u : G} (hu : u ∈ Subgroup.zpowers b) :
    u = 1 ∨ u = b := by
  classical
  have hf : IsOfFinOrder b := isOfFinOrder_of_finite b
  rw [hf.mem_zpowers_iff_mem_range_orderOf, hb] at hu
  simp only [Finset.mem_image, Finset.mem_range] at hu
  obtain ⟨j,hj,rfl⟩ := hu
  have he : j = 0 ∨ j = 1 := by omega
  rcases he with rfl | rfl <;> simp

theorem sup_cases (S : Subgroup G) (b : G)
    (hbN : b ∈ Subgroup.normalizer (S : Set G)) (hb : orderOf b = 2)
    {u : G} (hu : u ∈ S ⊔ Subgroup.zpowers b) : u ∈ S ∨ u * b⁻¹ ∈ S := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left S (Subgroup.zpowers b)
    (Subgroup.zpowers_le_of_mem hbN)
  change u ∈ (↑(S ⊔ Subgroup.zpowers b) : Set G) at hu
  rw [hm] at hu
  obtain ⟨s,hs,t,ht,rfl⟩ := hu
  change s ∈ S at hs
  rcases zpowers_cases b hb ht with rfl | rfl
  · exact Or.inl (by simpa only [mul_one] using hs)
  · exact Or.inr (by simpa only [mul_assoc, mul_inv_cancel, mul_one] using hs)

theorem card_sup (S : Subgroup G) (b : G)
    (hbN : b ∈ Subgroup.normalizer (S : Set G)) (hb : orderOf b = 2) (hbS : b ∉ S) :
    Nat.card (S ⊔ Subgroup.zpowers b : Subgroup G) = Nat.card S * 2 := by
  let Q : Subgroup G := S ⊔ Subgroup.zpowers b
  let T := S.subgroupOf Q
  let bQ : Q := ⟨b, (show Subgroup.zpowers b ≤ Q from le_sup_right) (Subgroup.mem_zpowers b)⟩
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := (eq_inv_iff_mul_eq_one.mpr hb2).symm
  have hi : T.index = 2 := by
    apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨bQ, hbS, ?_⟩
    intro q
    rcases sup_cases S b hbN hb q.property with hq | hq
    · exact Or.inr hq
    · apply Or.inl
      change (q : G) * b ∈ S
      simpa only [hbinv] using hq
  have hcard : Nat.card T = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show S ≤ Q from le_sup_left)).toEquiv
  have hc := T.card_mul_index
  rw [hcard, hi] at hc
  exact hc.symm

private theorem square_mem (S : Subgroup G) (b : G)
    (hbN : b ∈ Subgroup.normalizer (S : Set G)) (hb : orderOf b = 2)
    {u : G} (hu : u ∈ S ⊔ Subgroup.zpowers b) : u * u ∈ S := by
  rcases sup_cases S b hbN hb hu with hs | hs
  · exact S.mul_mem hs hs
  · have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
    have hconj : b * (u * b⁻¹) * b⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hbN _).mp hs
    have hm := S.mul_mem hs hconj
    have he : (u * b⁻¹) * (b * (u * b⁻¹) * b⁻¹) = u * u := by
      have hbinv : b⁻¹ = b := (eq_inv_iff_mul_eq_one.mpr hb2).symm
      calc
        _ = (u * u) * (b⁻¹ * b⁻¹) := by group
        _ = u * u := by rw [hbinv,hb2,mul_one]
    rwa [he] at hm

theorem fourth_power_eq_one (S : Subgroup G) (h2 : ∀ s : S, s * s = 1)
    (b : G) (hbN : b ∈ Subgroup.normalizer (S : Set G)) (hb : orderOf b = 2)
    {u : G} (hu : u ∈ S ⊔ Subgroup.zpowers b) : u ^ 4 = 1 := by
  have h := congrArg Subtype.val (h2 ⟨u * u, square_mem S b hbN hb hu⟩)
  change (u * u) * (u * u) = 1 at h
  simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two] using h

end FiveTransitive.InvolutiveNormalizerExtension

end CFSG
