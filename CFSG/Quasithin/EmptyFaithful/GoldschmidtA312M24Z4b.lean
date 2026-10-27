module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z4a

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open scoped Pointwise commutatorElement

@[expose] noncomputable def rho4 :
    ↥Z4 →* Equiv.Perm (Fin L4m.length) :=
  listHom Z4 L4m L4m_nodup Z4_inv

@[expose] def img4 (ws : List (List ℕ)) : List (List ℕ) :=
  ws.map (fun w => indTab actSetSet L4m (wordTab 24 gens4T w))

@[expose] def wS4 : List (List ℕ) := [[0], [1], [2], [3]]

theorem enum4_S : EnumOK 7 (img4 wS4) (bfsL 7 (img4 wS4) 100).1 (bfsL 7 (img4 wS4) 100).2 := by
  decide +kernel

theorem len4_S : (bfsL 7 (img4 wS4) 100).1.length = 8 := by decide +kernel

theorem enum4_3 : EnumOK 7 (img4 [[0, 4]]) (bfsL 7 (img4 [[0, 4]]) 100).1
    (bfsL 7 (img4 [[0, 4]]) 100).2 := by decide +kernel

theorem len4_3 : (bfsL 7 (img4 [[0, 4]]) 100).1.length = 3 := by decide +kernel

theorem enum4_7 : EnumOK 7 (img4 [[4]]) (bfsL 7 (img4 [[4]]) 100).1
    (bfsL 7 (img4 [[4]]) 100).2 := by decide +kernel

theorem len4_7 : (bfsL 7 (img4 [[4]]) 100).1.length = 7 := by decide +kernel

theorem rho4_dvd : 168 ∣ Nat.card rho4.range := by
  have hn : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ l ∈ w, l < 5) →
      ∀ {Lg par}, EnumOK 7 (img4 ws) Lg par → Lg.length ∣ Nat.card rho4.range :=
    fun ws hws {Lg par} h => card_dvd_range_words actSetSet hact_setset L4m L4m_nodup Z4_inv
      gens4 gens4_mem gens4T gens4_tab ws (by rw [gens4_length]; exact hws) h
  have h8 := hn wS4 (by decide) enum4_S
  have h3 := hn [[0, 4]] (by decide) enum4_3
  have h7 := hn [[4]] (by decide) enum4_7
  rw [len4_S] at h8
  rw [len4_3] at h3
  rw [len4_7] at h7
  omega

@[expose] def V4w : List (List ℕ) := [[3], [0, 0], [0, 3, 0], [2, 3, 2], [0, 1, 2, 1], [1, 0, 1, 2]]

@[expose] def V4T : List (List ℕ) := V4w.map (wordTab 24 sTL)

@[expose] def V4 : Subgroup G24 := Subgroup.closure {x | x ∈ wordG m24Sg V4w}

theorem V4g_tab : (wordG m24Sg V4w).map (tab 24) = V4T := by
  rw [wordG_tab m24Sg V4w (by simp only [m24Sg_length]; decide), m24Sg_tab]
  rfl

@[expose] def V4L : List (List ℕ) := (bfsL 24 V4T 200).1

@[expose] def V4par : List (ℕ × ℕ) := (bfsL 24 V4T 200).2

@[expose] def u4T : List ℕ := wordTab 24 gens4T u4w

@[expose] def c1T : List ℕ :=
  [0, 6, 2, 3, 5, 4, 1, 7, 9, 8, 15, 14, 18, 13, 11, 10, 20, 21, 12, 19, 16, 17, 22, 23]

@[expose] def c2T : List ℕ :=
  [10, 4, 17, 21, 1, 6, 5, 15, 18, 12, 0, 13, 9, 11, 19, 7, 22, 2, 8, 14, 23, 3, 16, 20]

@[expose] def V4Check : Prop :=
  EnumOK 24 V4T V4L V4par ∧ V4L.length = 2 ^ 7 ∧ z0T ∈ V4L ∧ z0T ≠ List.range 24 ∧
    (∀ t ∈ V4L, compTab t z0T = compTab z0T t) ∧ compTab z0T z0T = List.range 24 ∧
    (∀ g ∈ V4T, compTab g g = List.range 24 ∨ compTab g g = z0T) ∧
    (∀ g ∈ V4T, ∀ h ∈ V4T,
      compTab g h = compTab h g ∨ compTab g h = compTab z0T (compTab h g)) ∧
    (∀ t ∈ V4L, (∀ g ∈ V4T, compTab t g = compTab g t) → t = List.range 24 ∨ t = z0T) ∧
    (∀ t ∈ V4T, ∀ x ∈ L4m, actSetSet t x = x) ∧
    (∀ t ∈ V4L, ∃ s ∈ V4L, compTab s u4T = compTab (compTab t u4T) s ∨
      compTab s u4T = compTab (compTab (compTab t z0T) u4T) s) ∧
    c1T ∈ V4L ∧ c2T ∈ V4L ∧ (∃ s ∈ V4L, compTab s u4T = compTab (compTab c1T u4T) s) ∧
    (∃ s ∈ V4L, compTab s u4T = compTab (compTab c2T u4T) s) ∧
    compTab c1T c2T = compTab z0T (compTab c2T c1T)

instance : Decidable V4Check := by unfold V4Check; infer_instance

theorem V4_check : V4Check := by decide +kernel

end CFSG.Quasithin.A312M24
