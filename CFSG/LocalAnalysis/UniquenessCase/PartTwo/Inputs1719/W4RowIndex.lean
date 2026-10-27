module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin Subgroup

theorem le_mParam_of_index_sq {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {Y : Subgroup (MulAut W)} {ρ : ℕ} (hY : ∃ t ∈ Y, orderOf t = 2)
    (h : ∀ t ∈ Y, orderOf t = 2 → 2 ^ (2 * ρ) ≤ (fixV (zpowers t)).index ^ 2) :
    ρ ≤ E3.mParam Y := by
  obtain ⟨t, htY, hto⟩ := hY
  have hEven : Even (Nat.card Y) := by
    have h2 : orderOf (⟨t, htY⟩ : ↥Y) = 2 := by rwa [Subgroup.orderOf_mk]
    rw [even_iff_two_dvd, ← h2]
    exact orderOf_dvd_natCard _
  unfold E3.mParam
  rw [if_pos hEven]
  refine le_csInf ⟨_, t, htY, hto, rfl⟩ ?_
  rintro n ⟨s, hsY, hso, rfl⟩
  obtain ⟨m, hm⟩ := CFSG.QuasithinUnique.Setup.X1.index_fixV_eq_two_pow hW (Subgroup.zpowers s)
  have hle := h s hsY hso
  rw [hm, ← pow_mul] at hle
  have hρm : ρ ≤ m := by
    have h2m : 2 * ρ ≤ m * 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
    omega
  rw [rkIdx, hm, padicValNat.prime_pow]
  exact hρm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
