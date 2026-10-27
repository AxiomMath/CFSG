module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PRev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Line

@[expose] def glueVert (ℓ : Line Γ) (c : ℤ) (g : G) (i : ℤ) : V :=
  if i ≤ c then ℓ.vert i else g • ℓ.vert (2 * c - i)

variable (ℓ : Line Γ) (c : ℤ) (g : G)

theorem glueVert_le {i : ℤ} (hi : i ≤ c) : glueVert ℓ c g i = ℓ.vert i := by
  simp [glueVert, hi]

theorem glueVert_ge (hc : g • ℓ.vert c = ℓ.vert c) {i : ℤ} (hi : c ≤ i) :
    glueVert ℓ c g i = g • ℓ.vert (2 * c - i) := by
  rcases hi.eq_or_lt with rfl | h
  · rw [glueVert_le ℓ c g le_rfl, show 2 * c - c = c by omega, hc]
  · simp [glueVert, not_le.2 h]

@[expose] def glue (F : FanTree Γ G) (hc : g • ℓ.vert c = ℓ.vert c)
    (hm : g • ℓ.vert (c - 1) ≠ ℓ.vert (c - 1)) : Line Γ where
  vert := glueVert ℓ c g
  adj i := by
    rcases lt_or_ge i c with h | h
    · rw [glueVert_le ℓ c g (i := i) (by omega), glueVert_le ℓ c g (i := i + 1) (by omega)]
      exact ℓ.adj i
    · rw [glueVert_ge ℓ c g hc h, glueVert_ge ℓ c g hc (i := i + 1) (by omega)]
      have := (F.adj_smul g _ _).2 (ℓ.adj_pred (2 * c - i))
      rwa [show 2 * c - (i + 1) = 2 * c - i - 1 by omega]
  nb i := by
    rcases lt_or_ge (i + 2) (c + 1) with h | h
    · rw [glueVert_le ℓ c g (i := i) (by omega), glueVert_le ℓ c g (i := i + 2) (by omega)]
      exact ℓ.nb i
    · rcases lt_or_ge i c with h1 | h1
      · have hi : i = c - 1 := by omega
        subst hi
        rw [glueVert_le ℓ c g (i := c - 1) (by omega),
          glueVert_ge ℓ c g hc (i := c - 1 + 2) (by omega),
          show 2 * c - (c - 1 + 2) = c - 1 by omega]
        exact fun h => hm h.symm
      · rw [glueVert_ge ℓ c g hc h1, glueVert_ge ℓ c g hc (i := i + 2) (by omega)]
        intro h
        have := ℓ.nb (2 * c - (i + 2))
        rw [show 2 * c - (i + 2) + 2 = 2 * c - i by omega] at this
        exact this (MulAction.injective g h).symm

variable (F : FanTree Γ G) (hc : g • ℓ.vert c = ℓ.vert c)
  (hm : g • ℓ.vert (c - 1) ≠ ℓ.vert (c - 1))

theorem glue_vert_le {i : ℤ} (hi : i ≤ c) : (ℓ.glue c g F hc hm).vert i = ℓ.vert i :=
  glueVert_le ℓ c g hi

theorem glue_vert_ge {i : ℤ} (hi : c ≤ i) :
    (ℓ.glue c g F hc hm).vert i = g • ℓ.vert (2 * c - i) :=
  glueVert_ge ℓ c g hc hi

theorem glue_edgeCirc_le {i : ℤ} (hi : i + 1 ≤ c) :
    (ℓ.glue c g F hc hm).edgeCirc (G := G) i = ℓ.edgeCirc i := by
  rw [edgeCirc_eq_Ecirc, edgeCirc_eq_Ecirc, glue_vert_le ℓ c g F hc hm (i := i) (by omega),
    glue_vert_le ℓ c g F hc hm (i := i + 1) hi]

theorem glue_edgeCirc_cen {z : G} (hgz : g * z = z * g) {i j : ℤ} (hi : c ≤ i)
    (hj : j = 2 * c - i - 1) (hz : ∀ h ∈ ℓ.edgeCirc (G := G) j, h * z = z * h) :
    ∀ h ∈ (ℓ.glue c g F hc hm).edgeCirc (G := G) i, h * z = z * h := by
  intro h hh
  rw [edgeCirc_eq_Ecirc, glue_vert_ge ℓ c g F hc hm hi,
    glue_vert_ge ℓ c g F hc hm (i := i + 1) (by omega), show 2 * c - (i + 1) = j by omega,
    show 2 * c - i = j + 1 by omega] at hh
  have hadj : Γ.Adj (g • ℓ.vert (j + 1)) (g • ℓ.vert j) := by
    have := (F.adj_smul g _ _).2 (ℓ.adj j).symm
    exact this
  rw [F.Ecirc_comm hadj] at hh
  have h1 := F.Ecirc_smul g⁻¹ hh
  rw [inv_smul_smul, inv_smul_smul, inv_inv, ← edgeCirc_eq_Ecirc] at h1
  have c1 : Commute g z := hgz
  have c2 : Commute (g⁻¹ * h * g) z := hz _ h1
  have := (c1.mul_left c2).mul_left c1.inv_left
  rwa [show g * (g⁻¹ * h * g) * g⁻¹ = h by group] at this

end Line

end CFSG.Quasithin.Fan86
