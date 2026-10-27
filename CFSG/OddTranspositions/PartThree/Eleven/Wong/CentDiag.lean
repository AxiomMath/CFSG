module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentBasic

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SwapData

open Subgroup

variable {G : Type} [Group G] (D : SwapData G)

theorem d_apply (x : SL5) : D.d x = D.i1 x * D.i2 x := rfl

theorem i1_neg (x : SL5) : D.i1 (-x) = D.t * D.i1 x := by
  rw [← neg_one_mul, map_mul, ← D.t_eq_i1]

theorem i2_neg (x : SL5) : D.i2 (-x) = D.t * D.i2 x := by
  rw [← neg_one_mul, map_mul, ← D.t_eq_i2]

theorem d_commute_u (x : SL5) : Commute (D.d x) D.u := by
  have h : D.u⁻¹ * D.d x * D.u = D.d x := by
    rw [D.d_apply, D.u_conj_prod, (D.commute x x).eq]
  show D.d x * D.u = D.u * D.d x
  calc D.d x * D.u = D.u * (D.u⁻¹ * D.d x * D.u) := by group
    _ = D.u * D.d x := by rw [h]

theorem d_commute_t (x : SL5) : Commute (D.d x) D.t := by
  rw [D.d_apply]
  exact (D.t_commute_i1 x).symm.mul_left (D.t_commute_i2 x).symm

theorem t_ne_d (x : SL5) : D.t ≠ D.d x := by
  intro h
  have h' : D.i1 (-1) * D.i2 1 = D.i1 x * D.i2 x := by rw [map_one, mul_one, ← D.t_eq_i1, h]; rfl
  rcases D.prod_eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact sl5_neg_one_ne_one (h1.symm.trans h2)
  · rw [h2, neg_neg] at h1
    exact sl5_neg_one_ne_one h1

theorem d_mem_K (x : SL5) : D.d x ∈ D.K := D.mem_K_iff.mpr ⟨x, x, rfl⟩

theorem t_mem_K : D.t ∈ D.K := D.mem_K_iff.mpr ⟨-1, 1, by rw [map_one, mul_one, ← D.t_eq_i1]⟩

theorem t_mul_u_not_mem_K : D.t * D.u ∉ D.K := fun h => D.u_not_mem (by
  have := mul_mem (inv_mem D.t_mem_K) h
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)

theorem t_mem_normalizer_zpowers_u : D.t ∈ normalizer (zpowers D.u : Set G) := by
  refine mem_normalizer_iff.mpr fun g => ?_
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    rw [((D.t_commute_u.zpow_right k).eq), mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k
  · intro hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hg
    have hg' : g = D.u ^ k := calc
      g = D.t⁻¹ * (D.t * g * D.t⁻¹) * D.t := by group
      _ = D.t⁻¹ * D.u ^ k * D.t := by rw [hk]
      _ = D.u ^ k := by rw [mul_assoc, ← (D.t_commute_u.zpow_right k).eq, inv_mul_cancel_left]
    rw [hg']
    exact zpow_mem (mem_zpowers _) k

theorem mem_closure_t_u {g : G} (hg : g ∈ closure {D.t, D.u}) :
    g = 1 ∨ g = D.t ∨ g = D.u ∨ g = D.t * D.u := by
  have hle : zpowers D.t ≤ normalizer (zpowers D.u : Set G) :=
    zpowers_le.mpr D.t_mem_normalizer_zpowers_u
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_t).mp ha with rfl | rfl <;>
    rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_u).mp hb with rfl | rfl
  · exact Or.inl (one_mul 1)
  · exact Or.inr (Or.inr (Or.inl (one_mul _)))
  · exact Or.inr (Or.inl (mul_one _))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem closure_t_u_inf_A : closure {D.t, D.u} ⊓ D.A = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => ?_
  obtain ⟨hg1, x, rfl⟩ := mem_inf.mp hg
  rw [mem_bot]
  rcases D.mem_closure_t_u hg1 with h | h | h | h
  · exact h
  · exact absurd h.symm (D.t_ne_d x)
  · exact absurd (h ▸ D.d_mem_K x) D.u_not_mem
  · exact absurd (h ▸ D.d_mem_K x) D.t_mul_u_not_mem_K

private theorem swap_prod_eq {x y : SL5} (h : D.i1 y * D.i2 x = D.i1 x * D.i2 y) :
    D.i1 x * D.i2 y = D.d x ∨ D.i1 x * D.i2 y = D.t * D.d x := by
  rcases D.prod_eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
  · left
    rw [← h1]
    rfl
  · right
    rw [h2, D.i2_neg, D.d_apply, ← mul_assoc, ← (D.t_commute_i1 x).eq, mul_assoc]

private theorem prod_mem_of_commute_u {x y : SL5}
    (h : D.i1 x * D.i2 y * D.u = D.u * (D.i1 x * D.i2 y)) :
    D.i1 x * D.i2 y ∈ closure {D.t, D.u} ⊔ D.A := by
  have h' : D.i1 y * D.i2 x = D.i1 x * D.i2 y := by
    rw [← D.u_conj_prod, mul_assoc, h, inv_mul_cancel_left]
  rcases D.swap_prod_eq h' with h1 | h1 <;> rw [h1]
  · exact mem_sup_right ⟨x, rfl⟩
  · exact mul_mem (mem_sup_left (subset_closure (Set.mem_insert _ _))) (mem_sup_right ⟨x, rfl⟩)

theorem centralizer_t_inf_centralizer_u [Finite G] :
    centralizer {D.t} ⊓ centralizer {D.u} = closure {D.t, D.u} ⊔ D.A := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgt, hgu⟩ := mem_inf.mp hg
    rw [mem_centralizer_singleton_iff] at hgu
    rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
    · exact D.prod_mem_of_commute_u hgu
    · have h : D.i1 x * D.i2 y * D.u = D.u * (D.i1 x * D.i2 y) :=
        mul_right_cancel (b := D.u) (by simp only [mul_assoc] at hgu ⊢; exact hgu)
      exact mul_mem (D.prod_mem_of_commute_u h)
        (mem_sup_left (subset_closure (Set.mem_insert_of_mem _ rfl)))
  · refine sup_le ((closure_le _).mpr ?_) ?_
    · rintro g (rfl | rfl)
      · exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
          mem_centralizer_singleton_iff.mpr D.t_commute_u.eq⟩
      · exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr D.t_commute_u.eq.symm,
          mem_centralizer_singleton_iff.mpr rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (D.d_commute_t x).eq,
        mem_centralizer_singleton_iff.mpr (D.d_commute_u x).eq⟩

end CFSG.OddTranspositions.PartThree.Wong.SwapData
