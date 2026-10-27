module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.MaximalInvolutionFixedSet

open MulAction

theorem eq_one_of_fixing_outside
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : G)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hfix : ∀ q : Q, ∀ x ∈ fixedBy X t, q • x = x)
    (q : Q) (x : X) (hx : x ∉ fixedBy X t) (hqx : q • x = x) : q = 1 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hq
  let u : Q := q ^ (orderOf q / 2)
  have hu : orderOf u = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos q)) (hQ.dvd_orderOf hq)
  have huG : orderOf (u : G) = 2 := (Subgroup.orderOf_coe u).trans hu
  have hux : x ∈ fixedBy X (u : G) := by
    have hmem : q ∈ stabilizer Q x := hqx
    have hp := (stabilizer Q x).pow_mem hmem (orderOf q / 2)
    exact hp
  have hsub : fixedBy X t ⊆ fixedBy X (u : G) := by
    intro y hy
    exact hfix u y hy
  have hstrict : fixedBy X t ⊂ fixedBy X (u : G) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    exact hx (heq.symm ▸ hux)
  exact (not_lt_of_ge (hmax (u : G) huG)) (Set.ncard_lt_ncard hstrict)

theorem exists_sylow_fixing_set
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : G) (ht : orderOf t = 2)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard) :
    let H := fixingSubgroup G (fixedBy X t)
    ∃ Q : Sylow 2 H,
      (∃ q : Q, ((q : H) : G) = t) ∧
      fixedPoints Q X = fixedBy X t ∧
      ∀ (q : Q) (x : X), x ∉ fixedBy X t → q • x = x → q = 1 := by
  classical
  dsimp only
  let H := fixingSubgroup G (fixedBy X t)
  let tH : H := ⟨t, (mem_fixingSubgroup_iff G).mpr (fun x hx => hx)⟩
  have htH : orderOf tH = 2 := (Subgroup.orderOf_coe tH).symm.trans ht
  have hC : IsPGroup 2 (Subgroup.zpowers tH) :=
    IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers, htH, pow_one])
  obtain ⟨Q, hQ⟩ := hC.exists_le_sylow
  have htQ : tH ∈ Q := hQ (Subgroup.mem_zpowers tH)
  let tQ : Q := ⟨tH, htQ⟩
  refine ⟨Q, ⟨tQ, rfl⟩, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      exact (mem_fixedPoints.mp hx) tQ
    · intro hx
      rw [mem_fixedPoints]
      intro q
      exact (mem_fixingSubgroup_iff G).mp (q : H).property x hx
  · intro q x hx hqx
    have hmaxH : ∀ u : H, orderOf u = 2 →
        (fixedBy X u).ncard ≤ (fixedBy X tH).ncard := by
      intro u hu
      exact hmax (u : G) ((Subgroup.orderOf_coe u).trans hu)
    apply eq_one_of_fixing_outside H X tH hmaxH (Q : Subgroup H) Q.isPGroup' ?_ q x hx hqx
    intro u y hy
    exact (mem_fixingSubgroup_iff G).mp (u : H).property y hy

theorem exists_maximal_involution
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t₀ : G) (ht₀ : orderOf t₀ = 2) :
    ∃ t : G, orderOf t = 2 ∧
      (fixedBy X t₀).ncard ≤ (fixedBy X t).ncard ∧
      ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard := by
  classical
  let _ := Fintype.ofFinite G
  let s := Finset.univ.filter (fun u : G => orderOf u = 2)
  have hs : s.Nonempty := ⟨t₀, by simp [s, ht₀]⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image s (fun u : G => (fixedBy X u).ncard) hs
  have ht2 : orderOf t = 2 := (Finset.mem_filter.mp ht).2
  have hm : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard := by
    intro u hu
    exact hmax u (by simp [s, hu])
  exact ⟨t, ht2, hm t₀ ht₀, hm⟩

end FiveTransitive.MaximalInvolutionFixedSet

end CFSG
