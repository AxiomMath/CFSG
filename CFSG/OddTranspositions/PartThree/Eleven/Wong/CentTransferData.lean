module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDerived
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentMhat

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

private theorem mem_W_iff {x : G} : x ∈ D.W ↔
    x = 1 ∨ x = D.u ∨ x = D.v ∨ x = D.u * D.v ∨ x = D.w ∨ x = D.u * D.w ∨
      x = D.v * D.w ∨ x = D.u * D.v * D.w := by
  have hW : D.W = closure {D.u, D.v} ⊔ zpowers D.w := by
    rw [show D.W = closure {D.u, D.v, D.w} from rfl, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.insert_union, Set.singleton_union]
  have hle : closure {D.u, D.v} ≤ normalizer (zpowers D.w : Set G) := by
    refine (closure_le _).mpr ?_
    rintro g (rfl | rfl)
    · refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun k hk => ?_)
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
      exact (D.commute_u_w.zpow_right n).eq.symm
    · refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun k hk => ?_)
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
      exact (D.commute_v_w.zpow_right n).eq.symm
  rw [hW, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul]
  constructor
  · rintro ⟨c, hc, y, hy, rfl⟩
    rcases mem_closure_pair D.orderOf_u D.orderOf_v D.commute_u_v hc with rfl | rfl | rfl | rfl
    · rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_w).mp hy with rfl | rfl
      · exact Or.inl (one_mul 1)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (one_mul D.w)))))
    · rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_w).mp hy with rfl | rfl
      · exact Or.inr (Or.inl (mul_one D.u))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_w).mp hy with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (mul_one D.v)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_w).mp hy with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mul_one (D.u * D.v)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
    · exact ⟨D.u, subset_closure (by simp), 1, one_mem _, mul_one D.u⟩
    · exact ⟨D.v, subset_closure (by simp), 1, one_mem _, mul_one D.v⟩
    · exact ⟨D.u * D.v, mul_mem (subset_closure (by simp)) (subset_closure (by simp)), 1,
        one_mem _, mul_one (D.u * D.v)⟩
    · exact ⟨1, one_mem _, D.w, mem_zpowers D.w, one_mul D.w⟩
    · exact ⟨D.u, subset_closure (by simp), D.w, mem_zpowers D.w, rfl⟩
    · exact ⟨D.v, subset_closure (by simp), D.w, mem_zpowers D.w, rfl⟩
    · exact ⟨D.u * D.v, mul_mem (subset_closure (by simp)) (subset_closure (by simp)), D.w,
        mem_zpowers D.w, rfl⟩

private theorem relIndex_two_cover {H K : Subgroup G} (h2 : H.relIndex K = 2) {t : G}
    (htK : t ∈ K) (htH : t ∉ H) : (K : Set G) ⊆ (H : Set G) ∪ t • (H : Set G) := by
  intro x hxK
  by_cases hxH : x ∈ H
  · exact Or.inl hxH
  · right
    have hIdx : (H.subgroupOf K).index = 2 := h2
    have ht' : (⟨t, htK⟩ : K) ∉ H.subgroupOf K := by rwa [Subgroup.mem_subgroupOf]
    have hx' : (⟨x, hxK⟩ : K) ∉ H.subgroupOf K := by rwa [Subgroup.mem_subgroupOf]
    have hmul' : (⟨t, htK⟩ * ⟨x, hxK⟩ : K) ∈ H.subgroupOf K := by
      rw [Subgroup.mul_mem_iff_of_index_two hIdx]
      exact iff_of_false ht' hx'
    have hmul : t * x ∈ H := by
      simpa using Subgroup.mem_subgroupOf.mp hmul'
    have ht2' : (⟨t, htK⟩ : K) ^ 2 ∈ H.subgroupOf K :=
      Subgroup.sq_mem_of_index_two hIdx _
    have ht2 : t ^ 2 ∈ H := by
      simpa using Subgroup.mem_subgroupOf.mp ht2'
    refine ⟨(t ^ 2)⁻¹ * (t * x), mul_mem (inv_mem ht2) hmul, ?_⟩
    simp only [smul_eq_mul]
    group

private theorem M_eq_map_Mh : D.M = D.Mh.map (MulAut.conj D.z⁻¹).toMonoidHom := by
  obtain ⟨m, hm⟩ := D.fusion_element_w_action
  have huw : D.z⁻¹ * (D.u * D.w) * D.z = D.u * D.v ^ (m.val + 1) * D.w := by
    rw [show D.z⁻¹ * (D.u * D.w) * D.z =
        (D.z⁻¹ * D.u * D.z) * (D.z⁻¹ * D.w * D.z) by group, D.z_u', hm]
    fin_cases m
    · simp only [Fin.val_zero, pow_zero, mul_one, zero_add, pow_one]
      calc (D.t * D.v) * (D.t * D.u * D.w)
          = D.t * (D.v * (D.t * (D.u * D.w))) := by group
        _ = D.t * (D.t * (D.v * (D.u * D.w))) := by rw [D.v_mul_t_mul (D.u * D.w)]
        _ = D.v * (D.u * D.w) := by rw [D.t_mul_t_mul]
        _ = D.u * (D.v * D.w) := by rw [D.v_mul_u_mul]
        _ = D.u * D.v * D.w := by group
    · simp only [Fin.val_one, pow_one]
      calc (D.t * D.v) * (D.t * D.u * D.v * D.w)
          = D.t * (D.v * (D.t * (D.u * (D.v * D.w)))) := by group
        _ = D.t * (D.t * (D.v * (D.u * (D.v * D.w)))) := by
              rw [D.v_mul_t_mul (D.u * (D.v * D.w))]
        _ = D.v * (D.u * (D.v * D.w)) := by rw [D.t_mul_t_mul]
        _ = D.u * (D.v * (D.v * D.w)) := by rw [D.v_mul_u_mul]
        _ = D.u * D.w := by rw [D.v_mul_v_mul]
        _ = D.u * D.v ^ (1 + 1) * D.w := by
              rw [show (1 : ℕ) + 1 = 2 from rfl, pow_two, D.v_mul_v, mul_one]
  have huv : D.u * D.v ^ (m.val + 1) ∈ closure ({D.a, D.b} : Set G) := by
    have ha : D.a ∈ closure ({D.a, D.b} : Set G) := subset_closure (by simp)
    have hb : D.b ∈ closure ({D.a, D.b} : Set G) := subset_closure (by simp)
    fin_cases m
    · rw [show D.u * D.v ^ (0 + 1) = D.a ^ 2 by rw [zero_add, pow_one, ← D.a_sq]]
      exact pow_mem ha 2
    · rw [show D.u * D.v ^ (1 + 1) = D.a ^ 3 * D.b by
        rw [show (1 : ℕ) + 1 = 2 from rfl, pow_two, D.v_mul_v, mul_one]
        rw [show D.u = D.a ^ 2 * D.v by rw [D.a_sq, mul_assoc, D.v_mul_v, mul_one]]
        rw [show D.a ^ 3 * D.b = D.a ^ 2 * D.v by
          rw [show D.a ^ 3 = D.a ^ 2 * D.a by rw [pow_succ], mul_assoc, D.a_mul_b]]]
      exact mul_mem (pow_mem ha 3) hb
  rw [show D.Mh = closure ({D.h1, D.h2, D.u * D.w} : Set G) from rfl, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv, D.z_conj_h1, D.z_conj_h2, huw]
  apply le_antisymm
  · rw [show D.M = closure ({D.a, D.b, D.w} : Set G) from rfl]
    refine (closure_le _).mpr ?_
    rintro g (rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · have h1 : D.u * D.v ^ (m.val + 1) ∈
          closure ({D.a, D.b, D.u * D.v ^ (m.val + 1) * D.w} : Set G) :=
        closure_mono (by rintro z (rfl | rfl) <;> simp) huv
      have h2 : D.u * D.v ^ (m.val + 1) * D.w ∈
          closure ({D.a, D.b, D.u * D.v ^ (m.val + 1) * D.w} : Set G) :=
        subset_closure (by simp)
      have hmem : (D.u * D.v ^ (m.val + 1))⁻¹ * (D.u * D.v ^ (m.val + 1) * D.w) ∈
          closure ({D.a, D.b, D.u * D.v ^ (m.val + 1) * D.w} : Set G) :=
        mul_mem (inv_mem h1) h2
      rw [show (D.u * D.v ^ (m.val + 1))⁻¹ * (D.u * D.v ^ (m.val + 1) * D.w) = D.w by
        group] at hmem
      exact hmem
  · refine (closure_le _).mpr ?_
    rintro g (rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (closure_mono (by rintro z (rfl | rfl) <;> simp) huv) (subset_closure (by simp))

theorem r_not_mem_M : D.r ∉ D.M := by
  rw [D.M_eq_map_Mh, Subgroup.mem_map]
  rintro ⟨k, hk, hkz⟩
  have hkr : k = D.r := by
    have hkz' : D.z⁻¹ * k * D.z = D.r := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hkz
    calc k = D.z * (D.z⁻¹ * k * D.z) * D.z⁻¹ := by group
      _ = D.z * D.r * D.z⁻¹ := by rw [hkz']
      _ = D.r := by
        conv_lhs => rw [← D.z_conj_r]
        group
  rw [hkr] at hk
  rcases D.mem_Mh_iff.mp hk with ⟨x, hx, y, hy, hxy | hxy⟩
  · exact D.t_mul_u_not_mem_K (by
      rw [show D.t * D.u = D.i1 x * D.i2 y from hxy]
      exact D.mem_K_iff.mpr ⟨x, y, rfl⟩)
  · have huw2 : D.u * D.w * (D.u * D.w) = 1 := by
      calc D.u * D.w * (D.u * D.w) = D.u * (D.w * D.u) * D.w := by group
        _ = D.u * (D.u * D.w) * D.w := by rw [D.commute_u_w.eq]
        _ = D.u * D.u * (D.w * D.w) := by group
        _ = 1 := by rw [D.u_mul_u, D.w_mul_w, mul_one]
    have htw : D.t * D.w = D.i1 x * D.i2 y := by
      have h := congrArg (fun z => z * (D.u * D.w)) hxy
      rw [mul_assoc, huw2, mul_one] at h
      rw [← h, show D.r = D.t * D.u from rfl]
      rw [show D.t * D.u * (D.u * D.w) = D.t * D.w by rw [mul_assoc, D.u_mul_u_mul]]
    have htwc : D.t * D.w = D.i1 (-cM) * D.i2 cM := by
      rw [show D.t = D.i1 (-1) from D.t_eq_i1,
        show D.w = D.i1 cM * D.i2 cM from rfl, ← mul_assoc, ← map_mul, neg_one_mul]
    have hxy' : (x = -cM ∧ y = cM) ∨ (x = cM ∧ y = -cM) := by
      have := (D.prod_eq_iff).mp (htwc ▸ htw)
      simpa using this
    have hxcomm : Commute x hM := by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
      exact (Commute.refl hM).zpow_left n
    rcases hxy' with ⟨hx1, -⟩ | ⟨hx1, -⟩
    · rw [hx1] at hxcomm
      exact absurd ((commute_hM_iff (-cM)).mp hxcomm) (by decide)
    · rw [hx1] at hxcomm
      exact absurd ((commute_hM_iff cM).mp hxcomm) (by decide)

private theorem card_M_eq : Nat.card D.M = 16 := by
  have h8 : Nat.card D.W ∣ Nat.card D.M := Subgroup.card_dvd_of_le D.W_le_M
  have h32 : Nat.card D.M ∣ Nat.card D.T := Subgroup.card_dvd_of_le D.M_le_T
  rw [D.card_W] at h8
  rw [D.card_T] at h32
  have haW : D.a ∉ D.W := fun h => D.a_mul_w_not_mem_W (mul_mem h (subset_closure (by simp)))
  have hrT : D.r ∈ D.T := D.r_mem_T
  have hne8 : Nat.card D.M ≠ 8 := fun h => haW (by
    have hEq : D.W = D.M := Subgroup.eq_of_le_of_card_ge D.W_le_M (by rw [h, D.card_W])
    rw [hEq]; exact subset_closure (by simp))
  have hne32 : Nat.card D.M ≠ 32 := fun h => D.r_not_mem_M (by
    have hEq : D.M = D.T := Subgroup.eq_of_le_of_card_ge D.M_le_T (by rw [h, D.card_T])
    rw [hEq]; exact hrT)
  obtain ⟨c, hc⟩ := h8
  obtain ⟨d, hd⟩ := h32
  have hcd : c * d = 4 := by nlinarith [hc, hd]
  have hc_le : c ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨d, hcd.symm⟩
  interval_cases c <;> omega

private theorem relIndex_W_M : D.W.relIndex D.M = 2 := by
  have h := Subgroup.relIndex_mul_card (H := D.W) (K := D.M)
  rw [inf_eq_left.mpr D.W_le_M, D.card_W, D.card_M_eq] at h
  omega

theorem relIndex_M_T : D.M.relIndex D.T = 2 := by
  have h := Subgroup.relIndex_mul_card (H := D.M) (K := D.T)
  rw [inf_eq_left.mpr D.M_le_T, D.card_M_eq, D.card_T] at h
  omega

private theorem conj_a_of_mem_M : ∀ y ∈ D.M, y * D.a * y⁻¹ = D.a ∨
    y * D.a * y⁻¹ = D.a * D.v := by
  intro y hy
  have haM : D.a ∈ D.M := subset_closure (by simp)
  have hcom : ⁅y, D.a⁆ ∈ zpowers D.v := by
    have hmem : ⁅(⟨y, hy⟩ : D.M), (⟨D.a, haM⟩ : D.M)⁆ ∈ commutator D.M :=
      Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) trivial trivial
    have hmap : D.M.subtype ⁅(⟨y, hy⟩ : D.M), (⟨D.a, haM⟩ : D.M)⁆ ∈
        (commutator D.M).map D.M.subtype := ⟨_, hmem, rfl⟩
    rw [D.commutator_M_eq] at hmap
    rw [map_commutatorElement] at hmap
    simpa using hmap
  have hconj : y * D.a * y⁻¹ = ⁅y, D.a⁆ * D.a := by
    simpa only [MulAut.conj_apply] using conj_eq_commutatorElement_mul (g₁ := y) (g₂ := D.a)
  rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_v).mp hcom with h | h
  · left; rw [hconj, h, one_mul]
  · right; rw [hconj, h, (mem_centralizer_singleton_iff.mp (mem_inf.mp D.a_mem_T).2).symm]

private theorem involutions_M : ∀ x ∈ D.M, orderOf x = 2 ↔
    x = D.u ∨ x = D.v ∨ x = D.w ∨ x = D.v * D.w ∨ x = D.u * D.v ∨ x = D.u * D.w ∨
      x = D.u * D.v * D.w := by
  intro x hxM
  constructor
  · intro hx2
    have hu1 : D.u ≠ 1 := by
      intro h
      have := D.orderOf_u
      rw [h, orderOf_one] at this
      norm_num at this
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    have hx2sq : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx2] at this
    have haM : D.a ∈ D.M := subset_closure (by simp)
    have haW : D.a ∉ D.W := fun h => D.a_mul_w_not_mem_W (mul_mem h (subset_closure (by simp)))
    rcases relIndex_two_cover D.relIndex_W_M haM haW hxM with hxW | ⟨y, hyW, hxy⟩
    · rcases D.mem_W_iff.mp hxW with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hx1
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    · exfalso
      have hxy' : D.a * y = x := by simpa only [smul_eq_mul] using hxy
      have hy2 : y * y = 1 := by
        rw [← pow_two]
        exact D.sq_eq_one_of_mem_E (D.W_le_E hyW)
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have hsq : x ^ 2 = D.u * D.v ∨ x ^ 2 = D.u := by
        rw [← hxy', pow_two,
          show D.a * y * (D.a * y) = D.a * (y * D.a * y⁻¹) by rw [hyinv]; group]
        rcases D.conj_a_of_mem_M y (D.W_le_M hyW) with h | h
        · left; rw [h, ← pow_two, D.a_sq]
        · right; rw [h, ← mul_assoc, ← pow_two, D.a_sq, mul_assoc, D.v_mul_v, mul_one]
      rcases hsq with h | h
      · rw [h] at hx2sq
        exact D.u_mul_v_ne_one hx2sq
      · rw [h] at hx2sq
        exact hu1 hx2sq
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact D.orderOf_u
    · exact D.orderOf_v
    · exact D.orderOf_w
    · have hW : D.v * D.w ∈ D.W :=
        mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      refine orderOf_eq_prime (D.sq_eq_one_of_mem_E (D.W_le_E hW)) ?_
      intro h
      have h' : D.w = D.v := by
        rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right D.v_mul_v]
      exact D.w_ne_v h'
    · have hW : D.u * D.v ∈ D.W :=
        mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      exact orderOf_eq_prime (D.sq_eq_one_of_mem_E (D.W_le_E hW)) D.u_mul_v_ne_one
    · have hW : D.u * D.w ∈ D.W :=
        mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      refine orderOf_eq_prime (D.sq_eq_one_of_mem_E (D.W_le_E hW)) ?_
      intro h
      have h' : D.u = D.w := by
        have h2 : D.w = D.u := by
          rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right D.u_mul_u]
        exact h2.symm
      exact D.u_not_mem (h' ▸ D.A_le_K (D.J_le_A (subset_closure (Set.mem_insert_of_mem _ rfl))))
    · have hW : D.u * D.v * D.w ∈ D.W :=
        mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
          (subset_closure (by simp))
      refine orderOf_eq_prime (D.sq_eq_one_of_mem_E (D.W_le_E hW)) ?_
      intro h
      have h' : D.u = D.v * D.w := by
        have h2 : D.u * (D.v * D.w) = 1 := by rw [← mul_assoc]; exact h
        have h3 : D.v * D.w = D.u := by
          rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right D.u_mul_u]
        exact h3.symm
      exact D.u_not_mem (h' ▸ D.A_le_K (mul_mem
        (D.J_le_A (subset_closure (Set.mem_insert _ _)))
        (D.J_le_A (subset_closure (Set.mem_insert_of_mem _ rfl)))))

theorem transfer_subgroup_data :
    Nat.card D.M = 16 ∧ Nat.card D.J = 4 ∧ Nat.card D.W = 8 ∧ D.M ≤ D.T ∧ D.W ≤ D.M ∧
    (commutator D.T).map D.T.subtype = closure {D.u, D.v} ∧
    (commutator D.M).map D.M.subtype = zpowers D.v ∧
    (∀ x ∈ D.M, orderOf x = 2 ↔ x = D.u ∨ x = D.v ∨ x = D.w ∨ x = D.v * D.w ∨
      x = D.u * D.v ∨ x = D.u * D.w ∨ x = D.u * D.v * D.w) ∧
    (D.W.subgroupOf D.T).Normal ∧
    ∀ x ∈ D.T, x ∈ D.M ∨ x ∈ D.r • (D.W : Set G) ∨ x ∈ (D.r * D.a * D.w) • (D.W : Set G) := by
  refine ⟨D.card_M_eq, D.card_J, D.card_W, D.M_le_T, D.W_le_M, D.commutator_T_eq,
    D.commutator_M_eq, D.involutions_M, D.W_normal_T, ?_⟩
  intro x hxT
  rcases relIndex_two_cover D.relIndex_M_T D.r_mem_T D.r_not_mem_M hxT with hxM | ⟨m, hmM, hmx⟩
  · exact Or.inl hxM
  · have haM : D.a ∈ D.M := subset_closure (by simp)
    rcases relIndex_two_cover D.relIndex_W_M (mul_mem haM (subset_closure (by simp)))
      D.a_mul_w_not_mem_W hmM with hmW | ⟨y, hyW, hmy⟩
    · exact Or.inr (Or.inl ⟨m, hmW, hmx⟩)
    · exact Or.inr (Or.inr ⟨y, hyW, by
        rw [← hmx, ← hmy]
        simp only [smul_eq_mul]
        group⟩)

end CFSG.OddTranspositions.PartThree.Wong.SplitData
