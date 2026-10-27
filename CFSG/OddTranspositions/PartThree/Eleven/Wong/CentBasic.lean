module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SwapData

open Subgroup

variable {G : Type} [Group G] (D : SwapData G)

theorem t_eq_i1 : D.t = D.i1 (-1) := eq_i1_neg_one D.inj1 D.orderOf_t D.range_inf

theorem t_eq_i2 : D.t = D.i2 (-1) := eq_i2_neg_one D.inj2 D.orderOf_t D.range_inf

theorem u_mul_u : D.u * D.u = 1 := by
  rw [← pow_two, ← D.orderOf_u, pow_orderOf_eq_one]

theorem u_inv : D.u⁻¹ = D.u := inv_eq_of_mul_eq_one_right D.u_mul_u

theorem t_mul_t : D.t * D.t = 1 := by
  rw [← pow_two, ← D.orderOf_t, pow_orderOf_eq_one]

theorem t_inv : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right D.t_mul_t

theorem u_mul_i1 (x : SL5) : D.u * D.i1 x = D.i2 x * D.u := by
  rw [← D.swap x, mul_assoc (D.u⁻¹ * D.i1 x), D.u_mul_u, mul_one, D.u_inv]

theorem u_mul_i2 (x : SL5) : D.u * D.i2 x = D.i1 x * D.u := by
  rw [← D.swap x, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

theorem u_conj_i2 (x : SL5) : D.u⁻¹ * D.i2 x * D.u = D.i1 x := by
  rw [D.u_inv, D.u_mul_i2, mul_assoc, D.u_mul_u, mul_one]

theorem u_conj_prod (x y : SL5) :
    D.u⁻¹ * (D.i1 x * D.i2 y) * D.u = D.i1 y * D.i2 x := by
  rw [show D.u⁻¹ * (D.i1 x * D.i2 y) * D.u = (D.u⁻¹ * D.i1 x * D.u) * (D.u⁻¹ * D.i2 y * D.u) by
    group, D.swap, D.u_conj_i2, (D.commute y x).eq]

theorem t_commute_i1 (x : SL5) : Commute D.t (D.i1 x) := by
  rw [D.t_eq_i1]
  exact ((Commute.neg_one_left x).map D.i1)

theorem t_commute_i2 (x : SL5) : Commute D.t (D.i2 x) := by
  rw [D.t_eq_i2]
  exact ((Commute.neg_one_left x).map D.i2)

theorem t_commute_u : Commute D.t D.u := by
  have h : D.u⁻¹ * D.t * D.u = D.t := by
    rw [D.t_eq_i1, D.swap, ← D.t_eq_i2, ← D.t_eq_i1]
  show D.t * D.u = D.u * D.t
  calc D.t * D.u = D.u * (D.u⁻¹ * D.t * D.u) := by group
    _ = D.u * D.t := by rw [h]

theorem u_mem_centralizer_t : D.u ∈ centralizer {D.t} :=
  mem_centralizer_singleton_iff.mpr D.t_commute_u.eq.symm

theorem centralizer_t [Finite G] :
    centralizer {D.t} = (D.i1.range ⊔ D.i2.range) ⊔ zpowers D.u :=
  (D.hyp.sup_zpowers_eq_centralizer D.u_mem_centralizer_t D.u_not_mem).symm

theorem mem_K_iff {g : G} : g ∈ D.K ↔ ∃ x y : SL5, D.i1 x * D.i2 y = g :=
  mem_sup_iff D.commute

theorem prod_eq_iff {x y x' y' : SL5} :
    D.i1 x * D.i2 y = D.i1 x' * D.i2 y' ↔ (x' = x ∧ y' = y) ∨ (x' = -x ∧ y' = -y) :=
  prodHom_eq_iff D.inj1 D.inj2 D.orderOf_t D.commute D.range_inf

theorem u_mem_normalizer_K : D.u ∈ normalizer (D.K : Set G) := by
  refine mem_normalizer_iff.mpr fun g => ?_
  rw [D.mem_K_iff, D.mem_K_iff]
  constructor
  · rintro ⟨x, y, rfl⟩
    refine ⟨y, x, ?_⟩
    rw [← D.u_conj_prod, D.u_inv]
  · rintro ⟨x, y, h⟩
    refine ⟨y, x, ?_⟩
    rw [← D.u_conj_prod, h, D.u_inv,
      show D.u * (D.u * g * D.u) * D.u = (D.u * D.u) * g * (D.u * D.u) by group, D.u_mul_u,
      one_mul, mul_one]

theorem mem_centralizer_t_iff [Finite G] {g : G} : g ∈ centralizer {D.t} ↔
    (∃ x y : SL5, D.i1 x * D.i2 y = g) ∨ ∃ x y : SL5, D.i1 x * D.i2 y * D.u = g := by
  have hle : zpowers D.u ≤ normalizer ((D.i1.range ⊔ D.i2.range : Subgroup G) : Set G) :=
    zpowers_le.mpr D.u_mem_normalizer_K
  rw [D.centralizer_t, sup_comm, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, k, hk, rfl⟩
    obtain ⟨x, y, rfl⟩ := D.mem_K_iff.mp hk
    rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_u).mp ha with rfl | rfl
    · exact Or.inl ⟨x, y, (one_mul _).symm⟩
    · refine Or.inr ⟨y, x, ?_⟩
      rw [← D.u_conj_prod, D.u_inv, mul_assoc _ D.u D.u, D.u_mul_u, mul_one]
  · rintro (⟨x, y, rfl⟩ | ⟨x, y, rfl⟩)
    · exact ⟨1, one_mem _, _, D.mem_K_iff.mpr ⟨x, y, rfl⟩, one_mul _⟩
    · refine ⟨D.u, mem_zpowers _, D.i1 y * D.i2 x, D.mem_K_iff.mpr ⟨y, x, rfl⟩, ?_⟩
      rw [← D.u_conj_prod y x, D.u_inv, mul_assoc _ D.u D.u, D.u_mul_u, mul_one]

end CFSG.OddTranspositions.PartThree.Wong.SwapData
