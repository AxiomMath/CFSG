module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z3a

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open scoped Pointwise commutatorElement

@[expose] noncomputable def rho3 :
    ↥Z3 →* Equiv.Perm (Fin T3.length) :=
  listHom Z3 T3 T3_nodup Z3_inv

@[expose] def img3 (ws : List (List ℕ)) : List (List ℕ) :=
  ws.map (fun w => indTab actSet T3 (wordTab 24 gens3T w))

@[expose] def wS3 : List (List ℕ) := [[0], [1], [2], [3]]

@[expose] def wE93 : List (List ℕ) := [[0, 4, 1, 3, 4, 0, 3, 1, 4], [4, 1, 4, 1, 0, 1, 0]]

theorem enum3_S : EnumOK 6 (img3 wS3) (bfsL 6 (img3 wS3) 200).1 (bfsL 6 (img3 wS3) 200).2 := by
  decide +kernel

theorem len3_S : (bfsL 6 (img3 wS3) 200).1.length = 16 := by decide +kernel

theorem enum3_E9 :
    EnumOK 6 (img3 wE93) (bfsL 6 (img3 wE93) 200).1 (bfsL 6 (img3 wE93) 200).2 := by
  decide +kernel

theorem len3_E9 : (bfsL 6 (img3 wE93) 200).1.length = 9 := by decide +kernel

theorem enum3_5 : EnumOK 6 (img3 [[4]]) (bfsL 6 (img3 [[4]]) 200).1
    (bfsL 6 (img3 [[4]]) 200).2 := by decide +kernel

theorem len3_5 : (bfsL 6 (img3 [[4]]) 200).1.length = 5 := by decide +kernel

theorem rho3_dvd : 720 ∣ Nat.card rho3.range := by
  have hn : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < 5) →
      ∀ {Lg par}, EnumOK 6 (img3 ws) Lg par → Lg.length ∣ Nat.card rho3.range :=
    fun ws hws {Lg par} h => card_dvd_range_words actSet hact_set T3 T3_nodup Z3_inv gens3
      gens3_mem gens3T gens3_tab ws (by rw [gens3_length]; exact hws) h
  have h16 := hn wS3 (by decide) enum3_S
  have h9 := hn wE93 (by decide) enum3_E9
  have h5 := hn [[4]] (by decide) enum3_5
  rw [len3_S] at h16
  rw [len3_E9] at h9
  rw [len3_5] at h5
  omega

@[expose] def V3w : List (List ℕ) :=
  [[1], [2, 1, 2], [3, 1, 3], [0, 2, 0, 2], [0, 3, 0, 3], [0, 0, 0, 1, 0]]

@[expose] def V3T : List (List ℕ) := V3w.map (wordTab 24 sTL)

@[expose] def V3 : Subgroup G24 := Subgroup.closure {x | x ∈ wordG m24Sg V3w}

theorem V3g_tab : (wordG m24Sg V3w).map (tab 24) = V3T := by
  rw [wordG_tab m24Sg V3w (by simp only [m24Sg_length]; decide), m24Sg_tab]
  rfl

@[expose] def V3L : List (List ℕ) := (bfsL 24 V3T 200).1

@[expose] def V3par : List (ℕ × ℕ) := (bfsL 24 V3T 200).2

@[expose] def ω3w : List ℕ := [3, 4, 3, 4, 3, 4, 3, 4]

@[expose] def ω3T : List ℕ := wordTab 24 gens3T ω3w

@[expose] def V3Check : Prop :=
  EnumOK 24 V3T V3L V3par ∧ V3L.length = 64 ∧
    (∀ g ∈ V3T, ∀ h ∈ V3T, compTab g h = compTab h g) ∧
    (∀ g ∈ V3T, compTab g g = List.range 24) ∧ (∀ t ∈ V3T, ∀ x ∈ T3, actSet t x = x) ∧
    (∀ t ∈ V3L, ∃ s ∈ V3L, compTab s ω3T = compTab (compTab t ω3T) s) ∧
    ∀ gt ∈ gens3T, (∀ t ∈ V3L, ∃ s ∈ V3L, compTab gt t = compTab s gt) ∧
      ∀ t ∈ V3L, ∃ s ∈ V3L, compTab t gt = compTab gt s

instance : Decidable V3Check := by unfold V3Check; infer_instance

theorem V3_check : V3Check := by decide +kernel

theorem V3_le_Z3 : V3 ≤ Z3 := by
  rw [V3, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact evalEltL_mem m24Sg (fun _ hx => Subgroup.subset_closure (List.mem_append_left _ hx)) w

theorem enumV3 :
    EnumOK 24 ((wordG m24Sg V3w).map (tab 24)) V3L V3par := by
  rw [V3g_tab]
  exact V3_check.1

theorem card_V3 : Nat.card V3 = 2 ^ 6 := by
  obtain ⟨-, hcard, -⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective
    (wordG m24Sg V3w) enumV3
  rw [V3, hcard, V3_check.2.1]
  norm_num

theorem V3_fix : ∀ v ∈ V3, ∀ x ∈ T3, v • x = x := by
  refine fix_of_gens _ T3 (fun g hg x hx => ?_)
  have hgT : tab 24 g ∈ V3T := by rw [← V3g_tab]; exact List.mem_map_of_mem hg
  rw [hact_set]
  obtain ⟨-, -, -, -, hfix, -⟩ := V3_check
  exact hfix _ hgT x hx

theorem V3_comm_all :
    ∀ x ∈ V3, ∀ y ∈ V3, x * y = y * x := by
  obtain ⟨-, -, hc, -⟩ := V3_check
  exact comm_of_gen_tabs (gens := wordG m24Sg V3w) (by rw [V3g_tab]; exact hc)

theorem V3_sq : ∀ x ∈ V3, x * x = 1 := by
  obtain ⟨-, -, hc, hsq, -⟩ := V3_check
  exact sq_of_gen_tabs (gens := wordG m24Sg V3w) (by rw [V3g_tab]; exact hc)
    (by rw [V3g_tab]; exact hsq)

theorem Z3_normalizes_V3 :
    Z3 ≤ Subgroup.normalizer (V3 : Set G24) := by
  obtain ⟨-, -, -, -, -, -, hn⟩ := V3_check
  exact closure_le_normalizer_of_enum gens3_tab (gensV := wordG m24Sg V3w) enumV3 hn

@[expose] def ω3 : G24 := evalEltL gens3 ω3w

theorem tab_ω3 : tab 24 ω3 = ω3T := by
  unfold ω3
  rw [tab_evalEltL _ _ (by simp only [gens3_length]; decide), gens3_tab]
  rfl

theorem ω3_mem : ω3 ∈ Z3 := evalEltL_mem gens3 gens3_mem ω3w

theorem ω3_pow : ω3 ^ 3 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_ω3, tab_one_L]
  decide +kernel

theorem ω3_ne : ω3 ≠ 1 := by
  intro h
  have := congrArg (tab 24) h
  rw [tab_ω3, tab_one_L] at this
  revert this
  decide +kernel

theorem ω3_fixT : ∀ x ∈ T3, actSet ω3T x = x := by decide +kernel

theorem ω3_fix : ∀ x ∈ T3, ω3 • x = x := by
  intro x hx
  rw [hact_set, tab_ω3]
  exact ω3_fixT x hx

theorem rho3_ω3 : rho3 ⟨ω3, ω3_mem⟩ = 1 :=
  listHom_eq_one_of_fix Z3 T3 T3_nodup Z3_inv _ ω3_fix

theorem V3_comm : ∀ v ∈ V3, ∃ x ∈ V3, ⁅x, ω3⁆ = v :=
  comm_surj_of_enum (gens := wordG m24Sg V3w) enumV3 tab_ω3 V3_check.2.2.2.2.2.1

end CFSG.Quasithin.A312M24
