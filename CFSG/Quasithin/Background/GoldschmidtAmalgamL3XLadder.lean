module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XBasic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VDesc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XFrat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace TypeIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIConfig V m p)

include c

omit [Finite D] in
theorem Vv_zero_ne_bot (h : GoldHyp3 A B z V) : Vv V (p 0) ≠ ⊥ := fun e => by
  have := h.card_Vv_A c.vtype_zero
  rw [e, Subgroup.card_bot] at this
  omega

omit [Finite D] in
theorem Vn_zero_eq : Vn V 0 (p 0) = Vv V (p 0) :=
  le_antisymm (Vn_le_iff.mpr fun l _ hd => by
      obtain rfl : p 0 = l := (dist_eq_zero_iff rfl).mp (Nat.eq_zero_of_le_zero hd)
      exact le_rfl)
    (Vv_le_Vn c.vtype_zero (by rw [CosetGeom.dist_self]))

omit [Finite D] in
theorem Zlab_even {i : ℕ} (hi : i ≤ m + 1) (he : Even i) : Zlab V z (p i) = Vv V (p i) :=
  Zlab_of_vtype_false (c.vtype_even hi he)

omit [Finite D] in
theorem Zlab_odd {i : ℕ} (hi : i ≤ m + 1) (ho : Odd i) : Zlab V z (p i) = Zv z (p i) :=
  Zlab_of_vtype_true (c.vtype_odd hi ho)

omit [Finite D] in
theorem Vn_succ_left (a : ℕ) : Vn V a (p 0) ≤ Vn V (a + 1) (p 1) :=
  Vn_le_iff.mpr fun l hl hd => Vv_le_Vn hl (by
    have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 1) (p 0) l
    have h2 : CosetGeom.dist (p 1) (p 0) = 1 := by
      rw [CosetGeom.dist_comm]
      exact dist_eq_one_iff_adj.mpr (c.adj (Nat.zero_le _))
    omega)

omit [Finite D] in
theorem Vn_succ_right (a : ℕ) : Vn V a (p 1) ≤ Vn V (a + 1) (p 0) :=
  Vn_le_iff.mpr fun l hl hd => Vv_le_Vn hl (by
    have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 0) (p 1) l
    have h2 : CosetGeom.dist (p 0) (p 1) = 1 :=
      dist_eq_one_iff_adj.mpr (c.adj (Nat.zero_le _))
    omega)

theorem Vn_le_stab_edge (h : GoldHyp3 A B z V) {n : ℕ} (hn : n ≤ m) :
    Vn V n (p 1) ≤ stab (p 0) ⊓ stab (p 1) := by
  have hd1 : CosetGeom.dist (p 1) (p 0) = 1 := by
    rw [CosetGeom.dist_comm]
    exact dist_eq_one_iff_adj.mpr (c.adj (Nat.zero_le _))
  refine le_inf (Vn_le_iff.mpr fun l hl hd => h.Vv_le_stab_A c.critDist_eq hl ?_)
    (Vn_le_iff.mpr fun l hl hd => h.Vv_le_stab_A c.critDist_eq hl ?_)
  · have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl l (p 1) (p 0)
    rw [CosetGeom.dist_comm l (p 1)] at h1
    omega
  · rw [CosetGeom.dist_comm]
    omega

theorem false_of_acts_trivially (h : GoldHyp3 A B z V) {a b' c' : ℕ} (hab : a + 1 ≤ b')
    (hbc : b' + 1 ≤ c') (hc : c' ≤ m) {u : D} (hu : u ∈ stab (p 0) ⊓ stab (p 1))
    (huQ : u ∉ ballStab 1 (p 0))
    (hY : ∀ w ∈ Vn V c' (p 0), u * w * u⁻¹ * w⁻¹ ∈ Vn V a (p 0)) : False := by
  have key : Vn V b' (p 1) = ⊥ := h.eq_bot_of_acts_trivially (c.adj (Nat.zero_le _))
    ((c.Vn_succ_left a).trans (Vn_mono hab (p 1))) ((c.Vn_succ_right b').trans (Vn_mono hbc (p 0)))
    (c.Vn_le_stab_edge h (by omega)) (h.stab_le_normalizer_Vn a (p 0))
    (h.stab_le_normalizer_Vn c' (p 0)) (h.stab_le_normalizer_Vn b' (p 1)) hu huQ hY
  apply c.Vv_zero_ne_bot h
  refine le_bot_iff.mp ?_
  rw [← key]
  exact (Vv_le_Vn c.vtype_zero (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)).trans
    ((c.Vn_succ_left a).trans (Vn_mono hab (p 1)))

theorem desc (h : GoldHyp3 A B z V) {j : ℕ} (hj : j + 2 ≤ m + 1) {H : Subgroup D}
    (hH : H ≤ ballStab 1 (p j))
    (hc : H ≤ Subgroup.centralizer (Zlab V z (p (j + 2)) : Set D)) :
    H ≤ ballStab 1 (p (j + 1)) := by
  have := h.le_ballStab_one_desc c.geo (i := j + 1) (by omega) (by omega) (H := H)
    (by simpa using hH) (by simpa using hc)
  exact this

omit [Finite D] in
theorem dist_zero {i : ℕ} (hi : i ≤ m + 1) : CosetGeom.dist (p 0) (p i) = i := by
  rw [c.geo 0 i (Nat.zero_le _) hi]
  omega

omit [Finite D] in
theorem adj_pred {i : ℕ} (hi : i ≤ m + 1) (h1 : 1 ≤ i) :
    (graph (A ⊔ B) A B).Adj (p i) (p (i - 1)) := by
  have := c.adj (i := i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at this
  exact this.symm

omit [Finite D] in
theorem adj' {i j : ℕ} (hij : j = i + 1) (hj : j ≤ m + 1) :
    (graph (A ⊔ B) A B).Adj (p i) (p j) := by
  subst hij
  exact c.adj (by omega)

end TypeIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
