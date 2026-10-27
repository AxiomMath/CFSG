module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.TwoGroupCosetFixedBound

open MulAction

theorem fixed_le
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (b : ℕ) (hbound : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ b)
    (A : Subgroup G) (hA : IsPGroup 2 A) (g : A) (hg : g ≠ 1) :
    (fixedBy X (g : G)).ncard ≤ b := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t : A := g ^ (orderOf g / 2)
  have ht : orderOf t = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos g)) (hA.dvd_orderOf hg)
  have hsub : fixedBy X (g : G) ⊆ fixedBy X (t : G) := by
    intro x hx
    have hgx : g ∈ stabilizer A x := hx
    exact (stabilizer A x).pow_mem hgx (orderOf g / 2)
  exact (Set.ncard_le_ncard hsub).trans
    (hbound (t : G) ((Subgroup.orderOf_coe t).trans ht))

theorem coset_fixed_inter
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (q : Q) (x : G) :
    fixedBy X ((q : G) * x) ∩ fixedPoints Q X =
      fixedBy X x ∩ fixedPoints Q X := by
  ext y
  constructor
  · rintro ⟨hy, hQy⟩
    refine ⟨?_, hQy⟩
    have hqy : (q : G) • y = y := mem_fixedPoints.mp hQy q
    change ((q : G) * x) • y = y at hy
    rw [mul_smul] at hy
    exact smul_left_cancel (q : G) (hy.trans hqy.symm)
  · rintro ⟨hy, hQy⟩
    refine ⟨?_, hQy⟩
    change ((q : G) * x) • y = y
    rw [mul_smul, (show x • y = y from hy)]
    exact mem_fixedPoints.mp hQy q

private theorem complementary_fixed_le
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (t b : ℕ) (hb : b ≤ t)
    (hbound : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ t)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (x : G) (hx : x ∈ A) (hxQ : x ∉ Q)
    (hlocal : (fixedBy X x ∩ fixedPoints Q X).ncard = t - b)
    (q : Q) : (fixedBy X ((q : G) * x) \ fixedPoints Q X).ncard ≤ b := by
  let g : A := ⟨(q : G) * x, A.mul_mem (hQA q.property) hx⟩
  have hg : g ≠ 1 := by
    intro he
    apply hxQ
    have he' : (q : G) * x = 1 := congrArg Subtype.val he
    have hxinv : x = (q : G)⁻¹ := eq_inv_of_mul_eq_one_right he'
    rw [hxinv]
    exact Q.inv_mem q.property
  have hc := fixed_le t hbound A hA g hg
  change (fixedBy X ((q : G) * x)).ncard ≤ t at hc
  have hi : (fixedBy X ((q : G) * x) ∩ fixedPoints Q X).ncard = t - b := by
    rw [coset_fixed_inter Q q x]
    exact hlocal
  have hs : (fixedBy X ((q : G) * x) \ fixedPoints Q X).ncard =
      (fixedBy X ((q : G) * x)).ncard -
        (fixedBy X ((q : G) * x) ∩ fixedPoints Q X).ncard :=
    by
      have he : fixedBy X ((q : G) * x) \ fixedPoints Q X =
          fixedBy X ((q : G) * x) \ (fixedBy X ((q : G) * x) ∩ fixedPoints Q X) := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_inter_iff]
        tauto
      rw [he]
      exact Set.ncard_sdiff Set.inter_subset_left
  omega

theorem seven_transposition_complement
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hbound : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (x : G) (hx : x ∈ A) (hxQ : x ∉ Q)
    (hlocal : (fixedBy X x ∩ fixedPoints Q X).ncard = 5)
    (q : Q) : (fixedBy X ((q : G) * x) \ fixedPoints Q X).ncard ≤ 2 := by
  exact complementary_fixed_le 7 2 (by decide) hbound Q A hQA hA x hx hxQ hlocal q

end FiveTransitive.TwoGroupCosetFixedBound

end CFSG
