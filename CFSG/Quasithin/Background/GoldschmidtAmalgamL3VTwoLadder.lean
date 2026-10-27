module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VTwoBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XFrat

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace TypeIIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIIConfig V m p)

include c

omit [Finite D] in
theorem Vn_succ_one (a : ℕ) : Vn V a (p 1) ≤ Vn V (a + 1) (p 2) :=
  Vn_le_iff.mpr fun l hl hd => Vv_le_Vn hl (by
    have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 2) (p 1) l
    have h2 : CosetGeom.dist (p 2) (p 1) = 1 := by
      rw [CosetGeom.dist_comm]
      exact dist_eq_one_iff_adj.mpr (c.adj (i := 1) (by have := c.eight_le; omega))
    omega)

omit [Finite D] in
theorem Vn_succ_two (a : ℕ) : Vn V a (p 2) ≤ Vn V (a + 1) (p 1) :=
  Vn_le_iff.mpr fun l hl hd => Vv_le_Vn hl (by
    have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 1) (p 2) l
    have h2 : CosetGeom.dist (p 1) (p 2) = 1 :=
      dist_eq_one_iff_adj.mpr (c.adj (i := 1) (by have := c.eight_le; omega))
    omega)

theorem Vn_le_stab_edge (h : GoldHyp3 A B z V) {n : ℕ} (hn : n ≤ m) :
    Vn V n (p 2) ≤ stab (p 1) ⊓ stab (p 2) := by
  have hd1 : CosetGeom.dist (p 2) (p 1) = 1 := by
    rw [CosetGeom.dist_comm]
    exact dist_eq_one_iff_adj.mpr (c.adj (i := 1) (by have := c.eight_le; omega))
  refine le_inf (Vn_le_iff.mpr fun l hl hd => h.Vv_le_stab_A c.critDist_eq hl ?_)
    (Vn_le_iff.mpr fun l hl hd => h.Vv_le_stab_A c.critDist_eq hl ?_)
  · have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl l (p 2) (p 1)
    rw [CosetGeom.dist_comm l (p 2)] at h1
    omega
  · rw [CosetGeom.dist_comm]
    omega

theorem false_of_acts_trivially (h : GoldHyp3 A B z V) {a b' c' : ℕ} (hab : a + 1 ≤ b')
    (hbc : b' + 1 ≤ c') (hc : c' ≤ m) {u : D} (hu : u ∈ stab (p 1) ⊓ stab (p 2))
    (huQ : u ∉ ballStab 1 (p 1))
    (hY : ∀ w ∈ Vn V c' (p 1), u * w * u⁻¹ * w⁻¹ ∈ Vn V a (p 1)) : False := by
  have hm := c.eight_le
  have key : Vn V b' (p 2) = ⊥ := h.eq_bot_of_acts_trivially (c.adj (i := 1) (by omega))
    ((c.Vn_succ_one a).trans (Vn_mono hab (p 2))) ((c.Vn_succ_two b').trans (Vn_mono hbc (p 1)))
    (c.Vn_le_stab_edge h (by omega)) (h.stab_le_normalizer_Vn a (p 1))
    (h.stab_le_normalizer_Vn c' (p 1)) (h.stab_le_normalizer_Vn b' (p 2)) hu huQ hY
  apply c.Vv_ne_bot h (i := 2) (by omega) (by decide)
  refine le_bot_iff.mp ?_
  rw [← key]
  exact Vv_le_Vn (c.vtype_even (by omega) (by decide)) (by rw [CosetGeom.dist_self]; omega)

end TypeIIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
