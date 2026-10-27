module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentZ
import CFSG.GH74.GLS.SP.GenOrder

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup

variable {G : Type} [Group G] (D : SplitData G)

private theorem map_conj_centralizer (c x : G) :
    (centralizer {x}).map (MulAut.conj c).toMonoidHom = centralizer {c * x * c⁻¹} := by
  ext g
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    calc c * k * c⁻¹ * (c * x * c⁻¹) = c * (k * x) * c⁻¹ := by group
      _ = c * (x * k) * c⁻¹ := by rw [hk]
      _ = c * x * c⁻¹ * (c * k * c⁻¹) := by group
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, by group⟩
    calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹ * g) * c := by rw [hg]
      _ = x * (c⁻¹ * g * c) := by group

private theorem centralizer_uv_inf_v :
    centralizer {D.u * D.v} ⊓ centralizer {D.v} = centralizer {D.u} ⊓ centralizer {D.v} := by
  ext g
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc g * D.u = g * (D.u * D.v) * D.v := by rw [mul_assoc, mul_assoc, D.v_mul_v, mul_one]
      _ = D.u * D.v * (g * D.v) := by rw [h1, mul_assoc]
      _ = D.u * g := by rw [h2, mul_assoc, D.v_mul_v_mul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]

theorem T_eq_map : D.T = (centralizer {D.t} ⊓ centralizer {D.v}).map
    (MulAut.conj D.z⁻¹).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ (MulAut.conj D.z⁻¹).toMonoidHom (MulAut.conj D.z⁻¹).injective,
    map_conj_centralizer,
    map_conj_centralizer, inv_inv, D.z_t', D.z_v', D.centralizer_uv_inf_v]
  rfl

theorem card_T [Finite G] : Nat.card D.T = 32 := by
  rw [D.T_eq_map, Subgroup.card_map_of_injective (MulAut.conj D.z⁻¹).injective,
    D.card_centralizer_t_inf_centralizer_v]

private theorem conj_z_apply (g : G) :
    (MulAut.conj D.z⁻¹).toMonoidHom g = D.z⁻¹ * g * D.z := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem z_conj_h1 : D.z⁻¹ * D.h1 * D.z = D.a := rfl

theorem z_conj_h2 : D.z⁻¹ * D.h2 * D.z = D.b := rfl

theorem T_eq_closure [Finite G] : D.T = closure {D.a, D.b, D.w, D.r} := by
  obtain ⟨m, hm⟩ := D.fusion_element_w_action
  rw [D.T_eq_map, D.centralizer_t_inf_centralizer_v, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, D.conj_z_apply, D.z_conj_r, D.z_conj_h1,
    D.z_conj_h2, hm]
  have hv : D.v = D.a * D.b := by
    rw [show D.a * D.b = D.z⁻¹ * (D.h1 * D.h2) * D.z by
      rw [← D.z_conj_h1, ← D.z_conj_h2]; group]
    exact D.z_v'.symm
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    rintro _ (rfl | rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · rw [show D.t * D.u = D.r from rfl, hv]
      exact mul_mem (mul_mem (subset_closure (by simp))
        (pow_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) _))
        (subset_closure (by simp))
  · refine (closure_le _).mpr ?_
    have hrv : D.r * (D.a * D.b) ^ m.val ∈ closure {D.r, D.a, D.b, D.t * D.u * D.v ^ m.val * D.w} :=
      mul_mem (subset_closure (by simp))
        (pow_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) _)
    rintro _ (rfl | rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · have hw : D.w = (D.r * (D.a * D.b) ^ m.val)⁻¹ * (D.t * D.u * D.v ^ m.val * D.w) := by
        rw [hv, show D.t * D.u = D.r from rfl]
        group
      have h := mul_mem (inv_mem hrv)
        (subset_closure (show D.t * D.u * D.v ^ m.val * D.w ∈
          ({D.r, D.a, D.b, D.t * D.u * D.v ^ m.val * D.w} : Set G) by simp))
      rwa [← hw] at h
    · exact subset_closure (by simp)

private theorem conj_z_mul (x y : G) :
    D.z⁻¹ * x * D.z * (D.z⁻¹ * y * D.z) = D.z⁻¹ * (x * y) * D.z := by group

private theorem conj_z_conj (x y : G) :
    (D.z⁻¹ * y * D.z)⁻¹ * (D.z⁻¹ * x * D.z) * (D.z⁻¹ * y * D.z) = D.z⁻¹ * (y⁻¹ * x * y) * D.z := by
  group

private theorem conj_mul_eq (a b x : G) : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by
  group

private theorem conj_eq_of_commute {a x : G} (h : Commute a x) : a⁻¹ * x * a = x := by
  rw [mul_assoc, ← h.eq, inv_mul_cancel_left]

theorem h1_sq : D.h1 ^ 2 = D.t := by
  rw [show D.h1 = D.i1 hM from rfl, ← map_pow, hM_sq, ← D.t_eq_i1]

theorem h2_sq : D.h2 ^ 2 = D.t := by
  rw [show D.h2 = D.i2 hM from rfl, ← map_pow, hM_sq, ← D.t_eq_i2]

theorem a_sq : D.a ^ 2 = D.u * D.v := by
  rw [← D.z_conj_h1, pow_two, conj_z_mul, ← pow_two, D.h1_sq, D.z_t']

theorem b_sq : D.b ^ 2 = D.u * D.v := by
  rw [← D.z_conj_h2, pow_two, conj_z_mul, ← pow_two, D.h2_sq, D.z_t']

theorem a_mul_b : D.a * D.b = D.v := by
  rw [← D.z_conj_h1, ← D.z_conj_h2, conj_z_mul]
  exact D.z_v'

theorem commute_a_b : Commute D.a D.b := by
  show D.a * D.b = D.b * D.a
  rw [← D.z_conj_h1, ← D.z_conj_h2, conj_z_mul, conj_z_mul,
    show D.h1 * D.h2 = D.h2 * D.h1 from (D.commute hM hM).eq]

theorem w_sq : D.w ^ 2 = 1 := by rw [pow_two, D.w_mul_w]

theorem r_sq : D.r ^ 2 = 1 := by
  rw [pow_two, show D.r = D.t * D.u from rfl]
  simp only [mul_assoc, D.u_mul_t_mul, D.t_mul_t_mul, D.u_mul_u]

theorem commute_w_r : Commute D.w D.r := D.commute_t_w.symm.mul_right D.commute_u_w.symm

private theorem z_conj_tuvw {m : Fin 2} (hm : D.z⁻¹ * D.w * D.z = D.t * D.u * D.v ^ m.val * D.w) :
    D.z⁻¹ * (D.t * D.u * D.v ^ m.val * D.w) * D.z = D.w := by
  have h : D.z⁻¹ * (D.t * D.u * D.v ^ m.val * D.w) * D.z =
      D.z⁻¹ * D.t * D.z * (D.z⁻¹ * D.u * D.z) * (D.z⁻¹ * D.v * D.z) ^ m.val *
        (D.z⁻¹ * D.w * D.z) := by
    rw [show (D.z⁻¹ * D.v * D.z) ^ m.val = D.z⁻¹ * D.v ^ m.val * D.z by
      simpa [conj_z_apply] using (map_pow (MulAut.conj D.z⁻¹).toMonoidHom D.v m.val).symm]
    group
  rw [h, D.z_t', D.z_u', D.z_v', hm]
  fin_cases m
  · simp only [pow_zero, mul_one, mul_assoc, D.v_mul_t_mul, D.u_mul_t_mul, D.t_mul_t_mul,
      D.v_mul_u_mul, D.u_mul_u_mul, D.v_mul_v_mul]
  · simp only [pow_one, mul_assoc, D.v_mul_t_mul, D.u_mul_t_mul, D.t_mul_t_mul, D.v_mul_u_mul,
      D.u_mul_u_mul, D.v_mul_v_mul]

private theorem commute_t_h1 : Commute D.t D.h1 := D.t_commute_i1 hM
private theorem commute_t_h2 : Commute D.t D.h2 := D.t_commute_i2 hM

private theorem commute_v_h1 : Commute D.v D.h1 :=
  (Commute.refl (D.i1 hM)).mul_left (D.commute hM hM).symm

private theorem commute_v_h2 : Commute D.v D.h2 :=
  (D.commute hM hM).mul_left (Commute.refl (D.i2 hM))

private theorem conj_w_h1 : D.w⁻¹ * D.h1 * D.w = D.h1⁻¹ := by
  have h1 : (D.i1 cM)⁻¹ * D.i1 hM * D.i1 cM = (D.i1 hM)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, cM_inv_mul_hM_mul_cM, map_inv]
  rw [show D.w = D.i1 cM * D.i2 cM from rfl, conj_mul_eq, show D.h1 = D.i1 hM from rfl, h1]
  exact conj_eq_of_commute (D.commute hM cM).inv_left.symm

private theorem conj_w_h2 : D.w⁻¹ * D.h2 * D.w = D.h2⁻¹ := by
  have h2 : (D.i2 cM)⁻¹ * D.i2 hM * D.i2 cM = (D.i2 hM)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, cM_inv_mul_hM_mul_cM, map_inv]
  rw [show D.w = D.i1 cM * D.i2 cM from rfl, conj_mul_eq, show D.h2 = D.i2 hM from rfl,
    conj_eq_of_commute (D.commute cM hM), h2]

private theorem y_conj_h1 (k : ℕ) :
    (D.t * D.u * D.v ^ k * D.w)⁻¹ * D.h1 * (D.t * D.u * D.v ^ k * D.w) = D.h2⁻¹ := by
  rw [conj_mul_eq, conj_mul_eq, conj_mul_eq, conj_eq_of_commute D.commute_t_h1,
    show D.u⁻¹ * D.h1 * D.u = D.h2 from D.swap hM,
    conj_eq_of_commute (D.commute_v_h2.pow_left k), D.conj_w_h2]

private theorem y_conj_h2 (k : ℕ) :
    (D.t * D.u * D.v ^ k * D.w)⁻¹ * D.h2 * (D.t * D.u * D.v ^ k * D.w) = D.h1⁻¹ := by
  rw [conj_mul_eq, conj_mul_eq, conj_mul_eq, conj_eq_of_commute D.commute_t_h2,
    show D.u⁻¹ * D.h2 * D.u = D.h1 from D.u_conj_i2 hM,
    conj_eq_of_commute (D.commute_v_h1.pow_left k), D.conj_w_h1]

theorem conj_w_a_and_b [Finite G] :
    D.w⁻¹ * D.a * D.w = D.b⁻¹ ∧ D.w⁻¹ * D.b * D.w = D.a⁻¹ := by
  obtain ⟨m, hm⟩ := D.fusion_element_w_action
  have hw := D.z_conj_tuvw hm
  constructor
  · rw [← hw, ← D.z_conj_h1, conj_z_conj, y_conj_h1, ← D.z_conj_h2]
    group
  · rw [← hw, ← D.z_conj_h2, conj_z_conj, y_conj_h2, ← D.z_conj_h1]
    group

theorem conj_r_a_and_b : D.r⁻¹ * D.a * D.r = D.b ∧ D.r⁻¹ * D.b * D.r = D.a := by
  constructor
  · rw [← D.z_conj_r, ← D.z_conj_h1, conj_z_conj, show D.r = D.t * D.u from rfl, conj_mul_eq,
      conj_eq_of_commute D.commute_t_h1, show D.u⁻¹ * D.h1 * D.u = D.h2 from D.swap hM]
    rfl
  · rw [← D.z_conj_r, ← D.z_conj_h2, conj_z_conj, show D.r = D.t * D.u from rfl, conj_mul_eq,
      conj_eq_of_commute D.commute_t_h2, show D.u⁻¹ * D.h2 * D.u = D.h1 from D.u_conj_i2 hM]
    rfl

theorem a_mem_T [Finite G] : D.a ∈ D.T := by rw [D.T_eq_closure]; exact subset_closure (by simp)
theorem b_mem_T [Finite G] : D.b ∈ D.T := by rw [D.T_eq_closure]; exact subset_closure (by simp)
theorem w_mem_T [Finite G] : D.w ∈ D.T := by rw [D.T_eq_closure]; exact subset_closure (by simp)
theorem r_mem_T [Finite G] : D.r ∈ D.T := by rw [D.T_eq_closure]; exact subset_closure (by simp)

theorem M_le_T [Finite G] : D.M ≤ D.T := by
  refine (closure_le _).mpr ?_
  rintro _ (rfl | rfl | rfl)
  exacts [D.a_mem_T, D.b_mem_T, D.w_mem_T]

theorem v_mem_M : D.v ∈ D.M := by
  rw [← D.a_mul_b]
  exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem u_mem_M : D.u ∈ D.M := by
  have h : D.u = D.a ^ 2 * D.v := by rw [D.a_sq, mul_assoc, D.v_mul_v, mul_one]
  rw [h]
  exact mul_mem (pow_mem (subset_closure (by simp)) 2) D.v_mem_M

theorem W_le_M : D.W ≤ D.M := by
  refine (closure_le _).mpr ?_
  rintro _ (rfl | rfl | rfl)
  exacts [D.u_mem_M, D.v_mem_M, subset_closure (by simp)]

theorem J_le_W : D.J ≤ D.W := by
  refine (closure_le _).mpr ?_
  rintro _ (rfl | rfl) <;> exact subset_closure (by simp)

theorem W_le_E : D.W ≤ D.E := by
  refine (closure_le _).mpr ?_
  rintro _ (rfl | rfl | rfl) <;> exact subset_closure (by simp)

theorem v_ne_u : D.v ≠ D.u := fun h => D.u_not_mem (by rw [← h]; exact D.d_mem_K hM)

theorem u_mul_v_ne_one : D.u * D.v ≠ 1 := fun h =>
  D.v_ne_u (by rw [eq_inv_of_mul_eq_one_right h, D.u_inv])

theorem u_mul_not_mem_K {k : G} (hk : k ∈ D.K) : D.u * k ∉ D.K := fun h =>
  D.u_not_mem (show D.u ∈ D.K by simpa using mul_mem h (inv_mem hk))

theorem card_W : Nat.card D.W = 8 := by
  have hW : D.W = closure {D.u, D.v} ⊔ zpowers D.w := by
    rw [show D.W = closure {D.u, D.v, D.w} from rfl, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.insert_union, Set.singleton_union]
  have hA : zpowers D.w ≤ normalizer (closure {D.u, D.v} : Set G) := by
    refine zpowers_le.mpr (centralizer_le_normalizer _ ?_)
    rw [centralizer_closure]
    refine mem_centralizer_iff.mpr ?_
    rintro _ (rfl | rfl)
    exacts [D.commute_u_w.eq, D.commute_v_w.eq]
  have hwK : D.w ∈ D.K := D.d_mem_K cM
  have hinf : closure {D.u, D.v} ⊓ zpowers D.w = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    obtain ⟨hg1, hg2⟩ := mem_inf.mp hg
    rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_w).mp hg2 with rfl | rfl
    · exact one_mem _
    · exfalso
      rcases mem_closure_pair D.orderOf_u D.orderOf_v D.commute_u_v hg1 with h | h | h | h
      · have h2 := D.orderOf_w
        rw [h, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      · exact D.u_not_mem (h ▸ hwK)
      · exact D.w_ne_v h
      · exact D.u_mul_not_mem_K (D.d_mem_K hM) (h ▸ hwK)
  rw [hW, CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hA hinf,
    card_closure_pair D.orderOf_u D.orderOf_v D.commute_u_v D.v_ne_u, Nat.card_zpowers,
    D.orderOf_w]

theorem a_mul_w_not_mem_W : D.a * D.w ∉ D.W := fun h => by
  have ha : D.a ∈ D.E := by
    have := mul_mem (D.W_le_E h) (subset_closure (show D.w ∈ ({D.t, D.u, D.v, D.w} : Set G) by
      simp) : D.w ∈ D.E)
    rwa [mul_assoc, D.w_mul_w, mul_one] at this
  exact D.u_mul_v_ne_one (D.a_sq ▸ D.sq_eq_one_of_mem_E ha)

private theorem conj_mem_W_of_gen [Finite G] {g : G} (hg : g ∈ ({D.a, D.b, D.w, D.r} : Set G)) :
    ∀ x ∈ ({D.u, D.v, D.w} : Set G), g * x * g⁻¹ ∈ D.W := by
  have hgT : g ∈ D.T := by rw [D.T_eq_closure]; exact subset_closure hg
  have hgu : g * D.u * g⁻¹ = D.u := by
    rw [mem_centralizer_singleton_iff.mp (mem_inf.mp hgT).1, mul_inv_cancel_right]
  have hgv : g * D.v * g⁻¹ = D.v := by
    rw [mem_centralizer_singleton_iff.mp (mem_inf.mp hgT).2, mul_inv_cancel_right]
  have hu : D.u ∈ D.W := subset_closure (by simp)
  have hv : D.v ∈ D.W := subset_closure (by simp)
  have hw : D.w ∈ D.W := subset_closure (by simp)
  rintro _ (rfl | rfl | rfl)
  · rwa [hgu]
  · rwa [hgv]
  · have hvv : D.v⁻¹ = D.v := inv_eq_of_mul_eq_one_right D.v_mul_v
    rcases hg with rfl | rfl | rfl | rfl
    · have h : D.a * D.w * D.a⁻¹ = D.w * D.v := by
        calc D.a * D.w * D.a⁻¹ = D.w * (D.w⁻¹ * D.a * D.w) * D.a⁻¹ := by group
          _ = D.w * (D.a * D.b)⁻¹ := by rw [D.conj_w_a_and_b.1]; group
          _ = D.w * D.v := by rw [D.a_mul_b, hvv]
      rw [h]
      exact mul_mem hw hv
    · have h : D.b * D.w * D.b⁻¹ = D.w * D.v := by
        calc D.b * D.w * D.b⁻¹ = D.w * (D.w⁻¹ * D.b * D.w) * D.b⁻¹ := by group
          _ = D.w * (D.b * D.a)⁻¹ := by rw [D.conj_w_a_and_b.2]; group
          _ = D.w * D.v := by rw [← D.commute_a_b.eq, D.a_mul_b, hvv]
      rw [h]
      exact mul_mem hw hv
    · exact mul_mem (mul_mem hw hw) (inv_mem hw)
    · rw [(D.commute_w_r.symm).eq, mul_inv_cancel_right]
      exact hw

theorem T_le_normalizer_W [Finite G] : D.T ≤ normalizer (D.W : Set G) := by
  rw [D.T_eq_closure]
  refine (closure_le _).mpr fun g hg => mem_normalizer_fintype fun x hx => ?_
  have hmap : D.W.map (MulAut.conj g).toMonoidHom ≤ D.W := by
    rw [show D.W = closure {D.u, D.v, D.w} from rfl, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact D.conj_mem_W_of_gen hg y hy
  exact hmap (mem_map_of_mem _ hx)

theorem W_normal_T [Finite G] : (D.W.subgroupOf D.T).Normal :=
  (normal_subgroupOf_iff_le_normalizer (D.W_le_M.trans D.M_le_T)).mpr D.T_le_normalizer_W
end CFSG.OddTranspositions.PartThree.Wong.SplitData
