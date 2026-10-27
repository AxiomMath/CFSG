module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z1a
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Glue

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def w2 : List ℕ :=
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
    0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]

@[expose] def y2T : List ℕ :=
  [18, 14, 9, 6, 20, 22, 23, 12, 19, 16, 5, 3, 11, 7, 0, 4, 15, 8, 13, 2, 21, 1, 10, 17]

@[expose] def y2 : G24 := evalEltL [m24a, m24b] w2

theorem tab_y2 : tab 24 y2 = y2T := by
  unfold y2
  rw [tab_evalEltL _ _ (by decide)]
  show wordTab 24 [tab 24 m24a, tab 24 m24b] w2 = y2T
  rw [m24_tab_a, m24_tab_b]
  decide +kernel

@[expose] def gens2 : List G24 := m24Sg ++ [y2]

@[expose] def Z2 : Subgroup G24 := Subgroup.closure {x | x ∈ gens2}

@[expose] def gens2T : List (List ℕ) := sTL ++ [y2T]

theorem gens2_tab : gens2.map (tab 24) = gens2T := by
  rw [gens2, gens2T, List.map_append, m24Sg_tab, List.map_cons, List.map_nil, tab_y2]

theorem gens2_mem : ∀ x ∈ gens2, x ∈ Z2 := fun _ hx => Subgroup.subset_closure hx

theorem gens2_length : gens2.length = 5 := by
  simp [gens2, m24Sg_length]

@[expose] def T2 : List (Finset ℕ) :=
  [[0, 2, 3, 7, 10, 15, 17, 21], [1, 4, 5, 6, 8, 9, 12, 18],
    [11, 13, 14, 16, 19, 20, 22, 23]].map List.toFinset

theorem T2_nodup : T2.Nodup := by decide

theorem T2_gens : ∀ t ∈ gens2T, ∀ x ∈ T2, actSet t x ∈ T2 := by decide +kernel

theorem Z2_inv : ∀ z ∈ Z2, ∀ x ∈ T2, z • x ∈ T2 :=
  inv_list_of_gens gens2 T2 fun g hg x hx => by
    rw [hact_set]
    exact T2_gens _ (by rw [← gens2_tab]; exact List.mem_map_of_mem hg) x hx

theorem Z2_ne_top : Z2 ≠ ⊤ := by
  intro h
  have hm : m24b ∈ Z2 := h ▸ Subgroup.mem_top _
  have h1 := Z2_inv _ hm ({0, 2, 3, 7, 10, 15, 17, 21} : Finset ℕ) (by decide)
  rw [hact_set, m24_tab_b] at h1
  revert h1
  decide +kernel

theorem y2_mem : y2 ∈ Z2 :=
  Subgroup.subset_closure (List.mem_append_right _ (List.mem_singleton_self _))

theorem y2_pow : y2 ^ 21 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_y2, tab_one_L]
  decide +kernel

@[expose] def u2 : G24 := y2 ^ 3

theorem u2_mem : u2 ∈ Z2 := Subgroup.pow_mem _ y2_mem 3

theorem order_u2 : orderOf u2 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · show (y2 ^ 3) ^ 7 = 1
    rw [← pow_mul]
    exact y2_pow
  · intro h
    have := congrArg (tab 24) h
    rw [u2, tab_pow_L, tab_y2, tab_one_L] at this
    revert this
    decide +kernel

@[expose] def wE92 : List (List ℕ) := [[0, 3, 4, 3, 2, 1, 4, 0], [0, 0, 4, 0, 3, 4, 0, 4, 0]]

@[expose] def E9T2 : List (List ℕ) := wE92.map (wordTab 24 gens2T)

@[expose] def E92 : Subgroup G24 := Subgroup.closure {x | x ∈ wordG gens2 wE92}

theorem E9g_tab : (wordG gens2 wE92).map (tab 24) = E9T2 := by
  rw [wordG_tab gens2 wE92 (by simp only [gens2_length]; decide), gens2_tab]
  rfl

theorem enumE92 : EnumOK 24 E9T2 (bfsL 24 E9T2 50).1 (bfsL 24 E9T2 50).2 := by decide +kernel

theorem lenE92 : (bfsL 24 E9T2 50).1.length = 9 := by decide +kernel

theorem E92_le_Z2 : E92 ≤ Z2 := by
  rw [E92, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact evalEltL_mem gens2 gens2_mem w

theorem card_E92 : Nat.card E92 = 9 := by
  obtain ⟨-, hcard, -⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective
    (wordG gens2 wE92) (by rw [E9g_tab]; exact enumE92)
  rw [E92, hcard]
  exact lenE92

theorem S_le_Z2 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    m24CtxE.S ≤ Z2 := by
  rw [← m24CtxE.hSeq, Z2, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure (List.mem_append_left _ hx)

theorem Z2_eq_Y2 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card Z2 = 64512 ∧ Z2 = m24CtxE.Y 2 := by
  obtain ⟨j, hj, hZ, hc⟩ := overgroup_member S_le_Z2 Z2_ne_top
  have h7 : 7 ∣ Nat.card Z2 := order_u2 ▸ Subgroup.orderOf_dvd_natCard Z2 u2_mem
  have h9 : 9 ∣ Nat.card Z2 := card_E92 ▸ Subgroup.card_dvd_of_le E92_le_Z2
  rw [hc] at h7 h9
  rcases idx_9_7 j hj h9 h7 with rfl | rfl
  · exfalso
    have hy : y1 ∈ Z2 := by
      rw [hZ, ← Z1_eq_Y1.2]
      exact y1_mem
    have h1 := Z2_inv _ hy ({0, 2, 3, 7, 10, 15, 17, 21} : Finset ℕ) (by decide)
    rw [hact_set, tab_y1] at h1
    revert h1
    decide +kernel
  · exact ⟨by rw [hc]; rfl, hZ⟩

@[expose] noncomputable def rho2 :
    ↥Z2 →* Equiv.Perm (Fin T2.length) :=
  listHom Z2 T2 T2_nodup Z2_inv

theorem rho2_y2 : rho2 ⟨y2, y2_mem⟩ ≠ 1 := by
  intro h
  have := listHom_val Z2 T2 T2_nodup Z2_inv ⟨y2, y2_mem⟩ ⟨0, by decide⟩
  rw [show listHom Z2 T2 T2_nodup Z2_inv ⟨y2, y2_mem⟩ = 1 from h] at this
  simp only [hact_set, tab_y2] at this
  revert this
  decide +kernel

theorem false_Z2 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z2) : False := by
  have : Group.IsSolvable (Equiv.Perm (Fin T2.length)) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  have hyA : y2 ∈ perfectCore Z2 := by
    have := odd_mem_perfectCore m24_S_isPGroup hB (hY ▸ y2_mem) (m := 21) (by norm_num) y2_pow
    rwa [hY] at this
  exact rho2_y2 (map_eq_one_of_mem_perfectCore rho2 y2_mem hyA)

end CFSG.Quasithin.A312M24
