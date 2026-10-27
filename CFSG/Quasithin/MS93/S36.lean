module

public import CFSG.Quasithin.MS93.S36Ext4
public import CFSG.Quasithin.MS93.S36Inputs

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ

namespace S36

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem s33i_of_ne (h33 : S33w) (hSp : S36Sp4Excl) (h : PUHyp M T L)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hb : critDist (puAmalgam h.le) = 2)
    (hVU : Vq M L ≠ Uq M T L) (α' : Vtx (puAmalgam h.le))
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    S33i h α' (Qv (puAmalgam h.le) (baseA _)) := by
  obtain ⟨hY1, hY2, hY3⟩ := s33Hyp_Q_of_ne h hXL hb hVU hc
  rcases h33 G M T L h α' hc _ hY1 hY2 hY3 fun _ _ _ => qv_le_centralizer_xm _ _ with hi | hii
  · exact hi
  · exact (hSp G M T L h hb hVU α' hc hY3 hii).elim

theorem uq_inf_dq_eq_bot (h : PUHyp M T L) (hZU : Zq M L ⊓ Uq M T L = ⊥) :
    Uq M T L ⊓ Dq M L = ⊥ := by
  rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
  exact hZU

end S36

open S36

theorem s36_of_ext (h32 : S32) (h33 : S33w) (hSp : S36Sp4Excl) : S36 := by
  have hExt := s36SL3Ext_holds
  intro G _ _ M T L h hb
  obtain ⟨-, hXL, hcases⟩ := h32 G M T L h
  have hi : Vq M L ≠ Uq M T L → ∀ α' : Vtx (puAmalgam h.le),
      IsCritical (puAmalgam h.le) (baseA _) α' → S33i h α' (Qv (puAmalgam h.le) (baseA _)) :=
    fun hVU α' hc => s33i_of_ne h33 hSp h hXL hb hVU α' hc
  have hZU : Vq M L ≠ Uq M T L → Zq M L ⊓ Uq M T L = ⊥ := by
    intro hVU
    obtain ⟨ψ, hψ⟩ := exists_critical_inr h hb
    obtain ⟨_, _, _, _, _, _, _, _, _, hZU, -⟩ := hi hVU _ ((isCritical_inr_iff h hb ψ).mpr hψ)
    exact hZU
  refine ⟨?_, ?_⟩
  · by_cases hVU : Vq M L = Uq M T L
    · exact Or.inl hVU
    · exact Or.inr (hExt G M T L h hb hVU hXL (hi hVU))
  · rcases hcases with h1 | h1 | h1 | h1 | h1 | ⟨k, hk⟩ | h1
    · exact Or.inl (uq_inf_dq_eq_bot h h1.2.1)
    · exact Or.inl (uq_inf_dq_eq_bot h h1.2.1)
    · exact Or.inl (uq_inf_dq_eq_bot h h1.2.1)
    · exact Or.inr (Or.inr (isSL3TwoNonsplit_of h hb h1))
    · exact Or.inl (uq_inf_dq_eq_bot h h1.2.1)
    · refine Or.inr (Or.inl ⟨k, ?_⟩)
      rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq]
      exact hk
    · by_cases hVU : Vq M L = Uq M T L
      · exact Or.inl (uq_inf_dq_eq_bot_of_g2 h hb h1 hVU)
      · exact Or.inl (uq_inf_dq_eq_bot h (hZU hVU))

theorem s36_of (h32 : S32) (h33 : S33w) (hSp : S36Sp4Excl) : S36 :=
  s36_of_ext h32 h33 hSp

end CFSG.Quasithin.MS93
