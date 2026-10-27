module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z4a

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped Pointwise

@[expose] def w6 : List ℕ :=
  [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0]

@[expose] def y6T : List ℕ :=
  [21, 5, 3, 10, 1, 6, 8, 7, 12, 9, 17, 14, 18, 23, 22, 0, 19, 15, 4, 11, 20, 2, 13, 16]

@[expose] def y6 : G24 := evalEltL [m24a, m24b] w6

theorem tab_y6 : tab 24 y6 = y6T := by
  unfold y6
  rw [tab_evalEltL _ _ (by decide)]
  show wordTab 24 [tab 24 m24a, tab 24 m24b] w6 = y6T
  rw [m24_tab_a, m24_tab_b]
  decide +kernel

@[expose] def gens6 : List G24 := m24Sg ++ [y6]

@[expose] def Z6 : Subgroup G24 := Subgroup.closure {x | x ∈ gens6}

@[expose] def gens6T : List (List ℕ) := sTL ++ [y6T]

theorem gens6_tab : gens6.map (tab 24) = gens6T := by
  rw [gens6, gens6T, List.map_append, m24Sg_tab, List.map_cons, List.map_nil, tab_y6]

theorem gens6_mem : ∀ x ∈ gens6, x ∈ Z6 := fun _ hx => Subgroup.subset_closure hx

theorem gens6_length : gens6.length = 5 := by
  simp [gens6, m24Sg_length]

@[expose] def L6m : List (Finset (Finset ℕ)) :=
  [[[1, 8], [4, 5], [6, 9], [12, 18]], [[1, 18], [4, 6], [5, 9], [8, 12]],
    [[1, 5], [4, 8], [6, 12], [9, 18]], [[1, 6], [4, 18], [5, 12], [8, 9]],
    [[1, 12], [4, 9], [5, 6], [8, 18]], [[1, 9], [4, 12], [5, 18], [6, 8]],
    [[1, 4], [5, 8], [6, 18], [9, 12]]].map mkM

theorem L6m_nodup : L6m.Nodup := by decide

theorem L6m_gens : ∀ t ∈ gens6T, ∀ x ∈ L6m, actSetSet t x ∈ L6m := by decide +kernel

theorem Z6_inv : ∀ z ∈ Z6, ∀ x ∈ L6m, z • x ∈ L6m :=
  inv_list_of_gens gens6 L6m fun g hg x hx => by
    rw [hact_setset]
    exact L6m_gens _ (by rw [← gens6_tab]; exact List.mem_map_of_mem hg) x hx

@[expose] def LOl : List (Finset ℕ) := [[1, 4, 5, 6, 8, 9, 12, 18].toFinset]

theorem LOl_gens : ∀ t ∈ gens6T, ∀ x ∈ LOl, actSet t x ∈ LOl := by decide +kernel

theorem Z6_invLO : ∀ z ∈ Z6, ∀ x ∈ LOl, z • x ∈ LOl :=
  inv_list_of_gens gens6 LOl fun g hg x hx => by
    rw [hact_set]
    exact LOl_gens _ (by rw [← gens6_tab]; exact List.mem_map_of_mem hg) x hx

theorem T2_gens6 : ∀ t ∈ gens6T, ∀ x ∈ T2, actSet t x ∈ T2 := by decide +kernel

theorem Z6_invT2 : ∀ z ∈ Z6, ∀ x ∈ T2, z • x ∈ T2 :=
  inv_list_of_gens gens6 T2 fun g hg x hx => by
    rw [hact_set]
    exact T2_gens6 _ (by rw [← gens6_tab]; exact List.mem_map_of_mem hg) x hx

theorem Z6_ne_top : Z6 ≠ ⊤ := by
  intro h
  have hm : m24b ∈ Z6 := h ▸ Subgroup.mem_top _
  have h1 := Z6_invLO _ hm ([1, 4, 5, 6, 8, 9, 12, 18].toFinset) (by decide)
  rw [hact_set, m24_tab_b] at h1
  revert h1
  decide +kernel

theorem y6_mem : y6 ∈ Z6 :=
  Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))

theorem y6_pow : y6 ^ 7 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_y6, tab_one_L]
  decide +kernel

theorem order_y6 : orderOf y6 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime y6_pow ?_
  intro h
  have := congrArg (tab 24) h
  rw [tab_y6, tab_one_L] at this
  revert this
  decide +kernel

theorem S_le_Z6 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    m24CtxE.S ≤ Z6 := by
  rw [← m24CtxE.hSeq, Z6, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure (List.mem_append_left _ hx)

theorem Z6_eq [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card Z6 = 21504 ∧ ∃ j, (j = 4 ∨ j = 6) ∧ Z6 = m24CtxE.Y j := by
  obtain ⟨j, hj, hZ, hc⟩ := overgroup_member S_le_Z6 Z6_ne_top
  have h7 : 7 ∣ Nat.card Z6 := order_y6 ▸ Subgroup.orderOf_dvd_natCard Z6 y6_mem
  rw [hc] at h7
  rcases idx_7 j hj h7 with rfl | rfl | rfl | rfl
  · exfalso
    have hy : y1 ∈ Z6 := by
      rw [hZ, ← Z1_eq_Y1.2]
      exact y1_mem
    have h1 := Z6_invT2 _ hy ({0, 2, 3, 7, 10, 15, 17, 21} : Finset ℕ) (by decide)
    rw [hact_set, tab_y1] at h1
    revert h1
    decide +kernel
  · exfalso
    have hy : y2 ∈ Z6 := by
      rw [hZ, ← Z2_eq_Y2.2]
      exact y2_mem
    have h1 := Z6_invLO _ hy ([1, 4, 5, 6, 8, 9, 12, 18].toFinset) (by decide)
    rw [hact_set, tab_y2] at h1
    revert h1
    decide +kernel
  · exact ⟨by rw [hc]; rfl, 4, Or.inl rfl, hZ⟩
  · exact ⟨by rw [hc]; rfl, 6, Or.inr rfl, hZ⟩

theorem Z4_ne_Z6 : Z4 ≠ Z6 := by
  intro h
  have hy : y4 ∈ Z6 := h ▸ y4_mem
  have h1 := Z6_invT2 _ hy ({0, 2, 3, 7, 10, 15, 17, 21} : Finset ℕ) (by decide)
  rw [hact_set, tab_y4] at h1
  revert h1
  decide +kernel

@[expose] def O23 : List (Finset ℕ) :=
  [[0, 2, 3, 7, 10, 15, 17, 21].toFinset, [11, 13, 14, 16, 19, 20, 22, 23].toFinset]

theorem O23_nodup : O23.Nodup := by decide

theorem O23_gens : ∀ t ∈ gens6T, ∀ x ∈ O23, actSet t x ∈ O23 := by decide +kernel

theorem Z6_inv23 : ∀ z ∈ Z6, ∀ x ∈ O23, z • x ∈ O23 :=
  inv_list_of_gens gens6 O23 fun g hg x hx => by
    rw [hact_set]
    exact O23_gens _ (by rw [← gens6_tab]; exact List.mem_map_of_mem hg) x hx

@[expose] noncomputable def rho6sw :
    ↥Z6 →* Equiv.Perm (Fin O23.length) :=
  listHom Z6 O23 O23_nodup Z6_inv23

@[expose] def s0 : G24 := evalEltL m24Sg [0]

theorem tab_s0 : tab 24 s0 = wordTab 24 sTL [0] := by
  unfold s0
  rw [tab_evalEltL _ _ (by simp only [m24Sg_length]; decide), m24Sg_tab]

theorem s0_mem : s0 ∈ Z6 :=
  evalEltL_mem m24Sg (fun _ hx => Subgroup.subset_closure (List.mem_append_left _ hx)) [0]

theorem rho6sw_s0 : rho6sw ⟨s0, s0_mem⟩ ≠ 1 := by
  intro h
  have := listHom_val Z6 O23 O23_nodup Z6_inv23 ⟨s0, s0_mem⟩ ⟨0, by decide⟩
  rw [show listHom Z6 O23 O23_nodup Z6_inv23 ⟨s0, s0_mem⟩ = 1 from h] at this
  simp only [hact_set, tab_s0] at this
  revert this
  decide +kernel

theorem Z6_not_perfect : perfectCore Z6 ≠ Z6 := by
  intro h
  have : Group.IsSolvable (Equiv.Perm (Fin O23.length)) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  exact rho6sw_s0 (map_eq_one_of_mem_perfectCore rho6sw s0_mem (by rw [h]; exact s0_mem))

end CFSG.Quasithin.A312M24
