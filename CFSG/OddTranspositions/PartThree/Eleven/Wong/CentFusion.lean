module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentLocal

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

theorem mem_closure_pair {G : Type*} [Group G] {a b g : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : Commute a b) (hg : g ∈ closure {a, b}) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have hle : zpowers a ≤ normalizer (zpowers b : Set G) := by
    refine zpowers_le.mpr (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun k hk => ?_))
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
    exact (hab.symm.zpow_left n).eq
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  rcases (mem_zpowers_of_orderOf_eq_two ha).mp hx with rfl | rfl <;>
    rcases (mem_zpowers_of_orderOf_eq_two hb).mp hy with rfl | rfl
  · exact Or.inl (one_mul 1)
  · exact Or.inr (Or.inr (Or.inl (one_mul _)))
  · exact Or.inr (Or.inl (mul_one _))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem neg_inv_of_sq_eq_neg_one {g : SL5} (hg : g ^ 2 = -1) : (-g)⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by rw [neg_mul, ← pow_two, hg, neg_neg])

theorem ne_neg_self (y : SL5) : y ≠ -y := by
  intro h
  apply sl5_neg_one_ne_one
  calc (-1 : SL5) = -y * y⁻¹ := by rw [neg_mul, mul_inv_cancel]
    _ = y * y⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel y

theorem eq_one_or_neg_one_of_commute {x : SL5} (h1 : hM * x = x * hM) (h2 : cM * x = x * cM) :
    x = 1 ∨ x = -1 := by
  rcases (hM_mul_eq_iff x).mp h1 with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

theorem prod_inv (x y : SL5) : (D.i1 x * D.i2 y)⁻¹ = D.i1 x⁻¹ * D.i2 y⁻¹ := by
  rw [mul_inv_rev, ← map_inv, ← map_inv, (D.commute x⁻¹ y⁻¹).eq]

theorem conj_prod (g g' x y : SL5) :
    D.i1 g * D.i2 g' * (D.i1 x * D.i2 y) * (D.i1 g * D.i2 g')⁻¹ =
      D.i1 (g * x * g⁻¹) * D.i2 (g' * y * g'⁻¹) := by
  rw [D.prod_inv, D.prod_mul_prod, D.prod_mul_prod]

theorem A_le_K : D.A ≤ D.K := by
  rintro _ ⟨x, rfl⟩
  exact D.d_mem_K x

theorem exists_conj_v_of_mem_K {x : G} (hx : x ∈ D.K) (hx2 : orderOf x = 2) (hxt : x ≠ D.t) :
    ∃ k ∈ D.K, k⁻¹ * D.v * k = x := by
  obtain ⟨a, b, rfl⟩ := D.mem_K_iff.mp hx
  have hsq : D.i1 (a * a) * D.i2 (b * b) = 1 := by
    have h := pow_orderOf_eq_one (D.i1 a * D.i2 b)
    rwa [hx2, pow_two, D.prod_mul_prod] at h
  rcases (prodHom_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp hsq with
    ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso
    rcases sl5_eq_one_or_neg_one_of_mul_self ha with rfl | rfl <;>
      rcases sl5_eq_one_or_neg_one_of_mul_self hb with rfl | rfl
    · rw [map_one, map_one, mul_one, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    · exact hxt (by rw [map_one, one_mul, D.t_eq_i2])
    · exact hxt (by rw [map_one, mul_one, D.t_eq_i1])
    · rw [← D.t_eq_i1, ← D.t_eq_i2, D.t_mul_t, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
  · obtain ⟨g, hg⟩ := exists_conj_hM_of_sq_eq_neg_one (by rw [pow_two]; exact ha)
    obtain ⟨g', hg'⟩ := exists_conj_hM_of_sq_eq_neg_one (by rw [pow_two]; exact hb)
    refine ⟨D.i1 g * D.i2 g', D.mem_K_iff.mpr ⟨g, g', rfl⟩, ?_⟩
    rw [show D.v = D.i1 (g * a * g⁻¹) * D.i2 (g' * b * g'⁻¹) by rw [hg, hg']; rfl,
      ← D.conj_prod]
    group

theorem conj_i1_neg_u {g : SL5} (hg : g ^ 2 = -1) :
    D.i1 (-g) * D.u * (D.i1 (-g))⁻¹ = D.t * D.d g * D.u := by
  rw [← map_inv, neg_inv_of_sq_eq_neg_one hg, mul_assoc, D.u_mul_i1, ← mul_assoc, D.i1_neg,
    D.d_apply, mul_assoc D.t]

theorem isConj_u_t_mul_u_mul_d {g : SL5} (hg : g ^ 2 = -1) :
    IsConj D.u (D.t * D.u * D.d g) := by
  refine isConj_iff.mpr ⟨D.i1 (-g), ?_⟩
  rw [D.conj_i1_neg_u hg, mul_assoc D.t D.u, ← (D.d_commute_u g).eq, ← mul_assoc]

theorem isConj_tu_u_mul_d {g : SL5} (hg : g ^ 2 = -1) : IsConj (D.t * D.u) (D.u * D.d g) := by
  refine isConj_iff.mpr ⟨D.i1 (-g), ?_⟩
  calc D.i1 (-g) * (D.t * D.u) * (D.i1 (-g))⁻¹
      = D.t * (D.i1 (-g) * D.u * (D.i1 (-g))⁻¹) := by
        rw [← mul_assoc, ← (D.t_commute_i1 (-g)).eq]
        group
    _ = D.u * D.d g := by
        rw [D.conj_i1_neg_u hg, ← mul_assoc, ← mul_assoc, D.t_mul_t, one_mul,
          (D.d_commute_u g).eq]

theorem exists_mul_of_mem_E {x : G} (hx : x ∈ D.E) :
    ∃ c ∈ closure {D.t, D.u}, ∃ j ∈ D.J, x = c * j := by
  rw [D.E_eq_sup, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
    (fun g hg => centralizer_le_normalizer _ (D.J_le_centralizer_closure_t_u hg)),
    Set.mem_mul] at hx
  obtain ⟨c, hc, j, hj, rfl⟩ := hx
  exact ⟨c, hc, j, hj, rfl⟩

private theorem eq_t_of_mem_K_of_isConj (hTU : ¬ IsConj D.t D.u) (huv : IsConj D.u D.v) {y : G}
    (hy : y ∈ D.K) (hy2 : orderOf y = 2) (h : IsConj D.t y) : y = D.t := by
  by_contra hne
  obtain ⟨k, -, hk⟩ := D.exists_conj_v_of_mem_K hy hy2 hne
  exact hTU (h.trans (huv.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩)).symm)

theorem isConj_t_iff_of_mem_E (hTU : ¬ IsConj D.t D.u) (htu : IsConj D.t (D.t * D.u))
    (huv : IsConj D.u D.v) {x : G} (hx : x ∈ D.E) (hx2 : orderOf x = 2) :
    IsConj D.t x ↔ x = D.t ∨ x = D.t * D.u ∨ x = D.u * D.v ∨ x = D.u * D.w ∨
      x = D.u * D.v * D.w := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc, j, hj, rfl⟩ := D.exists_mul_of_mem_E hx
    have hjK : j ∈ D.K := D.A_le_K (D.J_le_A hj)
    rcases D.mem_closure_t_u hc with rfl | rfl | rfl | rfl
    · exact Or.inl (D.eq_t_of_mem_K_of_isConj hTU huv (mul_mem (one_mem _) hjK) hx2 h)
    · exact Or.inl (D.eq_t_of_mem_K_of_isConj hTU huv (mul_mem D.t_mem_K hjK) hx2 h)
    · rcases mem_closure_pair D.orderOf_v D.orderOf_w D.commute_v_w hj with rfl | rfl | rfl | rfl
      · exact absurd (by simpa using h) hTU
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (mul_assoc _ _ _).symm)))
    · rcases mem_closure_pair D.orderOf_v D.orderOf_w D.commute_v_w hj with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (mul_one _))
      · exact absurd (h.trans (D.isConj_u_t_mul_u_mul_d hM_sq).symm) hTU
      · exact absurd (h.trans (D.isConj_u_t_mul_u_mul_d cM_sq).symm) hTU
      · have h' := D.isConj_u_t_mul_u_mul_d hM_mul_cM_sq
        rw [map_mul] at h'
        exact absurd (h.trans h'.symm) hTU
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact IsConj.refl _
    · exact htu
    · exact htu.trans (D.isConj_tu_u_mul_d hM_sq)
    · exact htu.trans (D.isConj_tu_u_mul_d cM_sq)
    · have h' := htu.trans (D.isConj_tu_u_mul_d hM_mul_cM_sq)
      rw [map_mul, ← mul_assoc] at h'
      exact h'

private theorem prod_mem_zpowers_t {x y : SL5} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    D.i1 x * D.i2 y ∈ zpowers D.t := by
  have ht := mem_zpowers D.t
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rw [map_one, map_one, mul_one]
    exact one_mem _
  · rwa [map_one, one_mul, ← D.t_eq_i2]
  · rwa [map_one, mul_one, ← D.t_eq_i1]
  · rw [← D.t_eq_i1, ← D.t_eq_i2]
    exact mul_mem ht ht

private theorem not_commute_h1_prod_u (x y : SL5) :
    D.h1 * (D.i1 x * D.i2 y * D.u) ≠ D.i1 x * D.i2 y * D.u * D.h1 := by
  intro h
  have h' : D.i1 (hM * x) * D.i2 y * D.u = D.i1 x * D.i2 (y * hM) * D.u := by
    calc D.i1 (hM * x) * D.i2 y * D.u = D.h1 * (D.i1 x * D.i2 y * D.u) := by
          rw [map_mul, show D.h1 = D.i1 hM from rfl]
          group
      _ = D.i1 x * D.i2 y * D.u * D.h1 := h
      _ = D.i1 x * D.i2 (y * hM) * D.u := by
          rw [show D.h1 = D.i1 hM from rfl, mul_assoc _ D.u, D.u_mul_i1, map_mul]
          group
  rcases D.prod_eq_iff.mp (mul_right_cancel h') with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact absurd (mul_eq_left.mp h2) (by decide)
  · rw [← mul_neg_one y] at h2
    exact absurd (mul_left_cancel h2) (by decide)

private theorem eq_one_or_neg_one_of_commute_i1 {x y : SL5}
    (hh : D.i1 hM * (D.i1 x * D.i2 y) = D.i1 x * D.i2 y * D.i1 hM)
    (hc : D.i1 cM * (D.i1 x * D.i2 y) = D.i1 x * D.i2 y * D.i1 cM) : x = 1 ∨ x = -1 := by
  have key : ∀ g : SL5, D.i1 g * (D.i1 x * D.i2 y) = D.i1 x * D.i2 y * D.i1 g →
      g * x = x * g := fun g h => by
    rw [show D.i1 g = D.i1 g * D.i2 1 by rw [map_one, mul_one], D.prod_mul_prod,
      D.prod_mul_prod, one_mul, mul_one] at h
    rcases D.prod_eq_iff.mp h.symm with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd h2 (ne_neg_self y)
  exact eq_one_or_neg_one_of_commute (key hM hh) (key cM hc)

private theorem eq_one_or_neg_one_of_commute_i2 {x y : SL5}
    (hh : D.i2 hM * (D.i1 x * D.i2 y) = D.i1 x * D.i2 y * D.i2 hM)
    (hc : D.i2 cM * (D.i1 x * D.i2 y) = D.i1 x * D.i2 y * D.i2 cM) : y = 1 ∨ y = -1 := by
  have key : ∀ g : SL5, D.i2 g * (D.i1 x * D.i2 y) = D.i1 x * D.i2 y * D.i2 g →
      g * y = y * g := fun g h => by
    rw [show D.i2 g = D.i1 1 * D.i2 g by rw [map_one, one_mul], D.prod_mul_prod,
      D.prod_mul_prod, one_mul, mul_one] at h
    rcases D.prod_eq_iff.mp h.symm with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 (ne_neg_self x)
  exact eq_one_or_neg_one_of_commute (key hM hh) (key cM hc)

theorem S_le_centralizer_t : D.S ≤ centralizer {D.t} := by
  refine (closure_le _).mpr ?_
  rintro g (rfl | rfl | rfl | rfl | rfl) <;> refine mem_centralizer_singleton_iff.mpr ?_
  exacts [(D.t_commute_i1 hM).eq.symm, (D.t_commute_i1 cM).eq.symm, (D.t_commute_i2 hM).eq.symm,
    (D.t_commute_i2 cM).eq.symm, D.t_commute_u.eq.symm]

theorem center_S [Finite G] : center D.S = (zpowers D.t).subgroupOf D.S := by
  ext ⟨g, hg⟩
  rw [mem_subgroupOf, mem_center_iff]
  have hcomm : ∀ k ∈ D.S, (∀ s : D.S, s * ⟨g, hg⟩ = ⟨g, hg⟩ * s) → k * g = g * k :=
    fun k hk h => congrArg Subtype.val (h ⟨k, hk⟩)
  constructor
  · intro h
    have hS : ∀ k ∈ ({D.h1, D.c1, D.h2, D.c2, D.u} : Set G), k * g = g * k :=
      fun k hk => hcomm k (subset_closure hk) h
    rcases D.mem_centralizer_t_iff.mp (D.S_le_centralizer_t hg) with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
    · exact D.prod_mem_zpowers_t
        (D.eq_one_or_neg_one_of_commute_i1 (hS (D.i1 hM) (Or.inl rfl))
          (hS (D.i1 cM) (Or.inr (Or.inl rfl))))
        (D.eq_one_or_neg_one_of_commute_i2 (hS (D.i2 hM) (Or.inr (Or.inr (Or.inl rfl))))
          (hS (D.i2 cM) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact absurd (hS D.h1 (Or.inl rfl)) (D.not_commute_h1_prod_u x y)
  · intro ht s
    refine Subtype.ext ?_
    change (s : G) * g = g * s
    have hst : (s : G) ∈ centralizer {D.t} := D.S_le_centralizer_t s.2
    have ht' : g ∈ zpowers D.t := ht
    rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_t).mp ht' with rfl | rfl
    · rw [mul_one, one_mul]
    · exact mem_centralizer_singleton_iff.mp hst

theorem commute_t_v : Commute D.t D.v := (D.d_commute_t hM).symm
theorem commute_t_w : Commute D.t D.w := (D.d_commute_t cM).symm
theorem commute_u_v : Commute D.u D.v := (D.d_commute_u hM).symm
theorem commute_u_w : Commute D.u D.w := (D.d_commute_u cM).symm

theorem v_mul_v : D.v * D.v = 1 := by
  rw [← pow_two, ← D.orderOf_v, pow_orderOf_eq_one]

theorem w_mul_w : D.w * D.w = 1 := by
  rw [← pow_two, ← D.orderOf_w, pow_orderOf_eq_one]

theorem u_mul_t : D.u * D.t = D.t * D.u := D.t_commute_u.eq.symm
theorem v_mul_u : D.v * D.u = D.u * D.v := D.commute_u_v.eq.symm
theorem w_mul_v : D.w * D.v = D.v * D.w := D.commute_v_w.eq.symm

theorem u_mul_t_mul (x : G) : D.u * (D.t * x) = D.t * (D.u * x) := D.t_commute_u.symm.left_comm x
theorem v_mul_t_mul (x : G) : D.v * (D.t * x) = D.t * (D.v * x) := D.commute_t_v.symm.left_comm x
theorem v_mul_u_mul (x : G) : D.v * (D.u * x) = D.u * (D.v * x) := D.commute_u_v.symm.left_comm x
theorem w_mul_u_mul (x : G) : D.w * (D.u * x) = D.u * (D.w * x) := D.commute_u_w.symm.left_comm x
theorem t_mul_t_mul (x : G) : D.t * (D.t * x) = x := by rw [← mul_assoc, D.t_mul_t, one_mul]
theorem u_mul_u_mul (x : G) : D.u * (D.u * x) = x := by rw [← mul_assoc, D.u_mul_u, one_mul]
theorem v_mul_v_mul (x : G) : D.v * (D.v * x) = x := by rw [← mul_assoc, D.v_mul_v, one_mul]
end SwapData

namespace SplitData

variable {G : Type} [Group G] (D : SplitData G)

theorem isConj_t_u_mul_d {g : SL5} (hg : g ^ 2 = -1) : IsConj D.t (D.u * D.d g) :=
  D.isConj_t_tu.trans (D.toSwapData.isConj_tu_u_mul_d hg)

theorem isConj_t_iff_of_mem_E {x : G} (hx : x ∈ D.E) (hx2 : orderOf x = 2) :
    IsConj D.t x ↔ x = D.t ∨ x = D.t * D.u ∨ x = D.u * D.v ∨ x = D.u * D.w ∨
      x = D.u * D.v * D.w :=
  D.toSwapData.isConj_t_iff_of_mem_E D.not_isConj_t_u D.isConj_t_tu D.isConj_u_v hx hx2

end SplitData

end CFSG.OddTranspositions.PartThree.Wong
