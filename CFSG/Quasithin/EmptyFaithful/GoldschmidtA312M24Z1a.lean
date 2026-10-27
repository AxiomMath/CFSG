module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Rho

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open scoped Pointwise

@[expose] def w1 : List ℕ :=
  [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,
    1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]

@[expose] def y1T : List ℕ :=
  [2, 1, 11, 16, 8, 5, 18, 0, 12, 9, 7, 10, 6, 15, 21, 3, 22, 14, 4, 17, 19, 20, 13, 23]

@[expose] def y1 : G24 := evalEltL [m24a, m24b] w1

theorem tab_y1 : tab 24 y1 = y1T := by
  unfold y1
  rw [tab_evalEltL _ _ (by decide)]
  show wordTab 24 [tab 24 m24a, tab 24 m24b] w1 = y1T
  rw [m24_tab_a, m24_tab_b]
  decide +kernel

@[expose] def gens1 : List G24 := m24Sg ++ [y1]

@[expose] def Z1 : Subgroup G24 := Subgroup.closure {x | x ∈ gens1}

@[expose] def gens1T : List (List ℕ) := sTL ++ [y1T]

theorem gens1_tab : gens1.map (tab 24) = gens1T := by
  rw [gens1, gens1T, List.map_append, m24Sg_tab, List.map_cons, List.map_nil, tab_y1]

@[expose] def LO : List ℕ := [1, 4, 5, 6, 8, 9, 12, 18]

theorem fixLO : ∀ t ∈ gens1T, (LO.toFinset).image (fun p => t.getD p p) = LO.toFinset := by
  decide +kernel

theorem LO_nodup : LO.Nodup := by decide

theorem Z1_fix :
    Z1 ≤ MulAction.stabilizer G24 (LO.toFinset : Finset ℕ) := by
  rw [Z1, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, hact_set]
  exact fixLO _ (by rw [← gens1_tab]; exact List.mem_map_of_mem hg)

theorem Z1_inv : ∀ z ∈ Z1, ∀ x ∈ LO, z • x ∈ LO := by
  intro z hz x hx
  have h := MulAction.mem_stabilizer_iff.mp (Z1_fix hz)
  have : z • x ∈ z • (LO.toFinset : Finset ℕ) :=
    Finset.smul_mem_smul_finset (List.mem_toFinset.mpr hx)
  rw [h] at this
  exact List.mem_toFinset.mp this

theorem Z1_ne_top : Z1 ≠ ⊤ := by
  intro h
  have hm : m24b ∈ Z1 := h ▸ Subgroup.mem_top _
  have h1 := MulAction.mem_stabilizer_iff.mp (Z1_fix hm)
  rw [hact_set, m24_tab_b] at h1
  revert h1
  decide +kernel

@[expose] def y7w : List ℕ := [0, 2, 4, 4]

@[expose] def y1s : G24 := evalEltL gens1 y7w

theorem y1s_mem : y1s ∈ Z1 :=
  evalEltL_mem gens1 (fun _ hx => Subgroup.subset_closure hx) y7w

theorem tab_y1s : tab 24 y1s = wordTab 24 gens1T y7w := by
  unfold y1s
  rw [tab_evalEltL _ _ (by simp [gens1, y7w, m24Sg_length]), gens1_tab]

theorem y1_pow : y1 ^ 5 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_y1, tab_one_L]
  decide +kernel

theorem y1s_pow : y1s ^ 7 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_y1s, tab_one_L]
  decide +kernel

theorem S_le_Z1 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    m24CtxE.S ≤ Z1 := by
  rw [← m24CtxE.hSeq, Z1, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure (List.mem_append_left _ hx)

theorem order_y1 : orderOf y1 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime y1_pow ?_
  intro h
  have := congrArg (tab 24) h
  rw [tab_y1, tab_one_L] at this
  revert this
  decide +kernel

theorem order_y1s : orderOf y1s = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime y1s_pow ?_
  intro h
  have := congrArg (tab 24) h
  rw [tab_y1s, tab_one_L] at this
  revert this
  decide +kernel

theorem y1_mem : y1 ∈ Z1 :=
  Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))

theorem Z1_eq_Y1 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card Z1 = 322560 ∧ Z1 = m24CtxE.Y 1 := by
  obtain ⟨j, hj, hZ, hc⟩ := overgroup_member S_le_Z1 Z1_ne_top
  have h5 : 5 ∣ Nat.card Z1 := order_y1 ▸ Subgroup.orderOf_dvd_natCard Z1 y1_mem
  have h7 : 7 ∣ Nat.card Z1 := order_y1s ▸ Subgroup.orderOf_dvd_natCard Z1 y1s_mem
  rw [hc] at h5 h7
  have hm : memIdx[j]! = 315 := idx_dvd_35 j hj h5 h7
  have hj1 : j = 1 := idx_315 j hj hm
  subst hj1
  exact ⟨by rw [hc]; rfl, hZ⟩

end CFSG.Quasithin.A312M24
