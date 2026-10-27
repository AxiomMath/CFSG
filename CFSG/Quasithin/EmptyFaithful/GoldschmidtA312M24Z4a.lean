module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24L3

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open scoped Pointwise

@[expose] def w4 : List ℕ :=
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]

@[expose] def y4T : List ℕ :=
  [10, 1, 13, 19, 6, 9, 8, 15, 5, 12, 11, 2, 18, 23, 3, 14, 20, 0, 4, 22, 16, 7, 17, 21]

@[expose] def y4 : G24 := evalEltL [m24a, m24b] w4

theorem tab_y4 : tab 24 y4 = y4T := by
  unfold y4
  rw [tab_evalEltL _ _ (by decide)]
  show wordTab 24 [tab 24 m24a, tab 24 m24b] w4 = y4T
  rw [m24_tab_a, m24_tab_b]
  decide +kernel

@[expose] def gens4 : List G24 := m24Sg ++ [y4]

@[expose] def Z4 : Subgroup G24 := Subgroup.closure {x | x ∈ gens4}

@[expose] def gens4T : List (List ℕ) := sTL ++ [y4T]

theorem gens4_tab : gens4.map (tab 24) = gens4T := by
  rw [gens4, gens4T, List.map_append, m24Sg_tab, List.map_cons, List.map_nil, tab_y4]

theorem gens4_mem : ∀ x ∈ gens4, x ∈ Z4 := fun _ hx => Subgroup.subset_closure hx

theorem gens4_length : gens4.length = 5 := by
  simp [gens4, m24Sg_length]

@[expose] def mkM (l : List (List ℕ)) : Finset (Finset ℕ) := (l.map List.toFinset).toFinset

@[expose] def L4m : List (Finset (Finset ℕ)) :=
  [[[1, 6], [4, 5], [8, 9], [12, 18]], [[1, 4], [5, 6], [8, 18], [9, 12]],
    [[1, 12], [4, 9], [5, 8], [6, 18]], [[1, 8], [4, 18], [5, 12], [6, 9]],
    [[1, 5], [4, 6], [8, 12], [9, 18]], [[1, 9], [4, 12], [5, 18], [6, 8]],
    [[1, 18], [4, 8], [5, 9], [6, 12]]].map mkM

theorem L4m_nodup : L4m.Nodup := by decide

theorem L4m_gens : ∀ t ∈ gens4T, ∀ x ∈ L4m, actSetSet t x ∈ L4m := by decide +kernel

theorem Z4_inv : ∀ z ∈ Z4, ∀ x ∈ L4m, z • x ∈ L4m :=
  inv_list_of_gens gens4 L4m fun g hg x hx => by
    rw [hact_setset]
    exact L4m_gens _ (by rw [← gens4_tab]; exact List.mem_map_of_mem hg) x hx

@[expose] def z0T : List ℕ :=
  [7, 1, 3, 2, 4, 5, 6, 0, 8, 9, 15, 14, 12, 19, 11, 10, 20, 21, 18, 13, 16, 17, 23, 22]

@[expose] def z0w : List ℕ := [1, 3, 1, 3]

@[expose] def z0 : G24 := evalEltL m24Sg z0w

theorem tab_z0 : tab 24 z0 = z0T := by
  unfold z0
  rw [tab_evalEltL _ _ (by simp only [m24Sg_length]; decide), m24Sg_tab]
  decide +kernel

theorem gens4_comm_z0 : ∀ t ∈ gens4T, compTab t z0T = compTab z0T t := by decide +kernel

theorem Z4_cent : Z4 ≤ Subgroup.centralizer ({z0} : Set G24) := by
  rw [Z4, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  apply comm_of_tab (n := 24)
  rw [tab_z0]
  exact gens4_comm_z0 _ (by rw [← gens4_tab]; exact List.mem_map_of_mem hg)

theorem not_comm_z0_a : compTab (tab 24 m24a) z0T ≠ compTab z0T (tab 24 m24a) := by
  rw [m24_tab_a]
  decide +kernel

theorem Z4_ne_top : Z4 ≠ ⊤ := by
  intro h
  have hm : m24a ∈ Z4 := h ▸ Subgroup.mem_top _
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Z4_cent hm)
  have h2 := congrArg (tab 24) h1
  rw [tab_mul, tab_mul, tab_z0] at h2
  exact not_comm_z0_a h2

theorem y4_mem : y4 ∈ Z4 :=
  Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))

@[expose] def u4w : List ℕ := [3, 4]

@[expose] def u4 : G24 := evalEltL gens4 u4w

theorem tab_u4 : tab 24 u4 = wordTab 24 gens4T u4w := by
  unfold u4
  rw [tab_evalEltL _ _ (by simp only [gens4_length]; decide), gens4_tab]

theorem u4_mem : u4 ∈ Z4 := evalEltL_mem gens4 gens4_mem u4w

theorem u4_pow : u4 ^ 7 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_u4, tab_one_L]
  decide +kernel

theorem order_u4 : orderOf u4 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime u4_pow ?_
  intro h
  have := congrArg (tab 24) h
  rw [tab_u4, tab_one_L] at this
  revert this
  decide +kernel

theorem S_le_Z4 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    m24CtxE.S ≤ Z4 := by
  rw [← m24CtxE.hSeq, Z4, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure (List.mem_append_left _ hx)

theorem y1_not_comm_z0 : compTab y1T z0T ≠ compTab z0T y1T := by decide +kernel

theorem y2_not_comm_z0 : compTab y2T z0T ≠ compTab z0T y2T := by decide +kernel

theorem Z4_eq [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card Z4 = 21504 ∧ ∃ j, (j = 4 ∨ j = 6) ∧ Z4 = m24CtxE.Y j := by
  obtain ⟨j, hj, hZ, hc⟩ := overgroup_member S_le_Z4 Z4_ne_top
  have h7 : 7 ∣ Nat.card Z4 := order_u4 ▸ Subgroup.orderOf_dvd_natCard Z4 u4_mem
  rw [hc] at h7
  rcases idx_7 j hj h7 with rfl | rfl | rfl | rfl
  · exfalso
    have hy : y1 ∈ Z4 := by
      rw [hZ, ← Z1_eq_Y1.2]
      exact y1_mem
    have h2 := congrArg (tab 24) (Subgroup.mem_centralizer_singleton_iff.mp (Z4_cent hy))
    rw [tab_mul, tab_mul, tab_y1, tab_z0] at h2
    exact y1_not_comm_z0 h2
  · exfalso
    have hy : y2 ∈ Z4 := by
      rw [hZ, ← Z2_eq_Y2.2]
      exact y2_mem
    have h2 := congrArg (tab 24) (Subgroup.mem_centralizer_singleton_iff.mp (Z4_cent hy))
    rw [tab_mul, tab_mul, tab_y2, tab_z0] at h2
    exact y2_not_comm_z0 h2
  · exact ⟨by rw [hc]; rfl, 4, Or.inl rfl, hZ⟩
  · exact ⟨by rw [hc]; rfl, 6, Or.inr rfl, hZ⟩

end CFSG.Quasithin.A312M24
