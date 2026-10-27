module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z1a
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Glue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Subs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open scoped Pointwise

@[expose] def w3 : List ℕ :=
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]

@[expose] def y3T : List ℕ :=
  [21, 2, 10, 15, 23, 13, 7, 17, 3, 0, 5, 11, 19, 1, 14, 4, 16, 12, 22, 6, 20, 18, 9, 8]

@[expose] def y3 : G24 := evalEltL [m24a, m24b] w3

theorem tab_y3 : tab 24 y3 = y3T := by
  unfold y3
  rw [tab_evalEltL _ _ (by decide)]
  show wordTab 24 [tab 24 m24a, tab 24 m24b] w3 = y3T
  rw [m24_tab_a, m24_tab_b]
  decide +kernel

@[expose] def gens3 : List G24 := m24Sg ++ [y3]

@[expose] def Z3 : Subgroup G24 := Subgroup.closure {x | x ∈ gens3}

@[expose] def gens3T : List (List ℕ) := sTL ++ [y3T]

theorem gens3_tab : gens3.map (tab 24) = gens3T := by
  rw [gens3, gens3T, List.map_append, m24Sg_tab, List.map_cons, List.map_nil, tab_y3]

theorem gens3_mem : ∀ x ∈ gens3, x ∈ Z3 := fun _ hx => Subgroup.subset_closure hx

theorem gens3_length : gens3.length = 5 := by
  simp [gens3, m24Sg_length]

@[expose] def T3 : List (Finset ℕ) :=
  [[0, 2, 3, 7], [1, 6, 8, 9], [4, 5, 12, 18], [10, 15, 17, 21], [11, 14, 16, 20],
    [13, 19, 22, 23]].map List.toFinset

theorem T3_nodup : T3.Nodup := by decide

theorem T3_gens : ∀ t ∈ gens3T, ∀ x ∈ T3, actSet t x ∈ T3 := by decide +kernel

theorem Z3_inv : ∀ z ∈ Z3, ∀ x ∈ T3, z • x ∈ T3 :=
  inv_list_of_gens gens3 T3 fun g hg x hx => by
    rw [hact_set]
    exact T3_gens _ (by rw [← gens3_tab]; exact List.mem_map_of_mem hg) x hx

theorem Z3_ne_top : Z3 ≠ ⊤ := by
  intro h
  have hm : m24b ∈ Z3 := h ▸ Subgroup.mem_top _
  have h1 := Z3_inv _ hm ({0, 2, 3, 7} : Finset ℕ) (by decide)
  rw [hact_set, m24_tab_b] at h1
  revert h1
  decide +kernel

theorem y3_pow : y3 ^ 5 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_y3, tab_one_L]
  decide +kernel

theorem order_y3 : orderOf y3 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime y3_pow ?_
  intro h
  have := congrArg (tab 24) h
  rw [tab_y3, tab_one_L] at this
  revert this
  decide +kernel

theorem y3_mem : y3 ∈ Z3 :=
  Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))

theorem S_le_Z3 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    m24CtxE.S ≤ Z3 := by
  rw [← m24CtxE.hSeq, Z3, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure (List.mem_append_left _ hx)

theorem Z3_eq_Y3 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card Z3 = 138240 ∧ Z3 = m24CtxE.Y 3 := by
  obtain ⟨j, hj, hZ, hc⟩ := overgroup_member S_le_Z3 Z3_ne_top
  have h5 : 5 ∣ Nat.card Z3 := order_y3 ▸ Subgroup.orderOf_dvd_natCard Z3 y3_mem
  rw [hc] at h5
  rcases idx_5 j hj h5 with rfl | rfl
  · exfalso
    have hy : y1 ∈ Z3 := by
      rw [hZ, ← Z1_eq_Y1.2]
      exact y1_mem
    have h1 := Z3_inv _ hy ({0, 2, 3, 7} : Finset ℕ) (by decide)
    rw [hact_set, tab_y1] at h1
    revert h1
    decide +kernel
  · exact ⟨by rw [hc]; rfl, hZ⟩

end CFSG.Quasithin.A312M24
