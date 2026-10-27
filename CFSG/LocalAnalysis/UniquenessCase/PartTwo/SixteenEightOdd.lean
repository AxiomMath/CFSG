module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_v1Sub_eq_of_inf_fixV (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥) : v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h0 : V₀ = ⊥
  · subst h0
    exact s16c167_v1Sub_eq_bot_of_inf_fixV D hV rfl h
  · exact v1Sub_of_ne_bot D.M V₀ V hV L h0

private theorem s16e_odd_rk_imgTil {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil V₀ V hV)) (V₁ : Subgroup G) (h : V₁ = V₀) :
    rk ↥(imgTil V₁ V hV (preTil V₀ V hV S)) = rk ↥S := by
  subst h
  rw [imgTil_preTil]

theorem s16e_gamma15_eq_of_inf_fixV (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥) :
    gamma15 D.M V₀ V hV L = rk ↥(wTil V₀ V hV L) :=
  s16e_odd_rk_imgTil hV (wTil V₀ V hV L) (v1Sub D.M V₀ V hV L)
    (s16e_v1Sub_eq_of_inf_fixV D hV h)

theorem s16e_v1Sub_eq_of_odd (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) : v1Sub D.M V₀ V hV L = V₀ :=
  s16e_v1Sub_eq_of_inf_fixV D hV (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd)

theorem s16e_gamma15_eq_of_odd (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) :
    gamma15 D.M V₀ V hV L = rk ↥(wTil V₀ V hV L) :=
  s16e_gamma15_eq_of_inf_fixV D hV (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
