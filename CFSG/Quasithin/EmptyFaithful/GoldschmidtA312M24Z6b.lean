module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z6a
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Subs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open scoped Pointwise commutatorElement

@[expose] noncomputable def rho6 :
    ↥Z6 →* Equiv.Perm (Fin L6m.length) :=
  listHom Z6 L6m L6m_nodup Z6_inv

@[expose] def img6 (ws : List (List ℕ)) : List (List ℕ) :=
  ws.map (fun w => indTab actSetSet L6m (wordTab 24 gens6T w))

@[expose] def wS6 : List (List ℕ) := [[0], [1], [2], [3]]

theorem enum6_S : EnumOK 7 (img6 wS6) (bfsL 7 (img6 wS6) 100).1 (bfsL 7 (img6 wS6) 100).2 := by
  decide +kernel

theorem len6_S : (bfsL 7 (img6 wS6) 100).1.length = 8 := by decide +kernel

theorem enum6_3 : EnumOK 7 (img6 [[0, 1, 4]]) (bfsL 7 (img6 [[0, 1, 4]]) 100).1
    (bfsL 7 (img6 [[0, 1, 4]]) 100).2 := by decide +kernel

theorem len6_3 : (bfsL 7 (img6 [[0, 1, 4]]) 100).1.length = 3 := by decide +kernel

theorem enum6_7 : EnumOK 7 (img6 [[4]]) (bfsL 7 (img6 [[4]]) 100).1
    (bfsL 7 (img6 [[4]]) 100).2 := by decide +kernel

theorem len6_7 : (bfsL 7 (img6 [[4]]) 100).1.length = 7 := by decide +kernel

theorem rho6_dvd : 168 ∣ Nat.card rho6.range := by
  have hn : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < 5) →
      ∀ {Lg par}, EnumOK 7 (img6 ws) Lg par → Lg.length ∣ Nat.card rho6.range :=
    fun ws hws {Lg par} h => card_dvd_range_words actSetSet hact_setset L6m L6m_nodup Z6_inv
      gens6 gens6_mem gens6T gens6_tab ws (by rw [gens6_length]; exact hws) h
  have h8 := hn wS6 (by decide) enum6_S
  have h3 := hn [[0, 1, 4]] (by decide) enum6_3
  have h7 := hn [[4]] (by decide) enum6_7
  rw [len6_S] at h8
  rw [len6_3] at h3
  rw [len6_7] at h7
  omega

@[expose] def V6w : List (List ℕ) :=
  [[0, 0], [0, 1, 0, 1], [0, 2, 0, 2], [0, 3, 0, 3], [1, 0, 0, 1], [0, 1, 2, 1, 2, 3]]

@[expose] def V6T : List (List ℕ) := V6w.map (wordTab 24 sTL)

@[expose] def V6 : Subgroup G24 := Subgroup.closure {x | x ∈ wordG m24Sg V6w}

theorem V6g_tab : (wordG m24Sg V6w).map (tab 24) = V6T := by
  rw [wordG_tab m24Sg V6w (by simp only [m24Sg_length]; decide), m24Sg_tab]
  rfl

@[expose] def V6L : List (List ℕ) := (bfsL 24 V6T 200).1

@[expose] def V6par : List (ℕ × ℕ) := (bfsL 24 V6T 200).2

@[expose] def V6Check : Prop :=
  EnumOK 24 V6T V6L V6par ∧ V6L.length = 64 ∧
    (∀ g ∈ V6T, ∀ h ∈ V6T, compTab g h = compTab h g) ∧
    (∀ g ∈ V6T, compTab g g = List.range 24) ∧ (∀ t ∈ V6T, ∀ x ∈ L6m, actSetSet t x = x) ∧
    (∀ t ∈ V6L, ∃ s ∈ V6L, compTab s y6T = compTab (compTab t y6T) s) ∧
    ∀ gt ∈ gens6T, (∀ t ∈ V6L, ∃ s ∈ V6L, compTab gt t = compTab s gt) ∧
      ∀ t ∈ V6L, ∃ s ∈ V6L, compTab t gt = compTab gt s

instance : Decidable V6Check := by unfold V6Check; infer_instance

theorem V6_check : V6Check := by decide +kernel

theorem V6_le_Z6 : V6 ≤ Z6 := by
  rw [V6, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact evalEltL_mem m24Sg (fun _ hx => Subgroup.subset_closure (List.mem_append_left _ hx)) w

theorem enumV6 :
    EnumOK 24 ((wordG m24Sg V6w).map (tab 24)) V6L V6par := by
  rw [V6g_tab]
  exact V6_check.1

theorem card_V6 : Nat.card V6 = 2 ^ 6 := by
  obtain ⟨-, hcard, -⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective
    (wordG m24Sg V6w) enumV6
  rw [V6, hcard, V6_check.2.1]
  norm_num

theorem V6_fix : ∀ v ∈ V6, ∀ x ∈ L6m, v • x = x := by
  refine fix_of_gens _ L6m (fun g hg x hx => ?_)
  have hgT : tab 24 g ∈ V6T := by rw [← V6g_tab]; exact List.mem_map_of_mem hg
  rw [hact_setset]
  obtain ⟨-, -, -, -, hfix, -⟩ := V6_check
  exact hfix _ hgT x hx

theorem V6_comm_all :
    ∀ x ∈ V6, ∀ y ∈ V6, x * y = y * x := by
  obtain ⟨-, -, hc, -⟩ := V6_check
  exact comm_of_gen_tabs (gens := wordG m24Sg V6w) (by rw [V6g_tab]; exact hc)

theorem V6_sq : ∀ x ∈ V6, x * x = 1 := by
  obtain ⟨-, -, hc, hsq, -⟩ := V6_check
  exact sq_of_gen_tabs (gens := wordG m24Sg V6w) (by rw [V6g_tab]; exact hc)
    (by rw [V6g_tab]; exact hsq)

theorem Z6_normalizes_V6 :
    Z6 ≤ Subgroup.normalizer (V6 : Set G24) := by
  obtain ⟨-, -, -, -, -, -, hn⟩ := V6_check
  exact closure_le_normalizer_of_enum gens6_tab (gensV := wordG m24Sg V6w) enumV6 hn

theorem V6_comm : ∀ v ∈ V6, ∃ x ∈ V6, ⁅x, y6⁆ = v :=
  comm_surj_of_enum (gens := wordG m24Sg V6w) enumV6 tab_y6 V6_check.2.2.2.2.2.1

end CFSG.Quasithin.A312M24
