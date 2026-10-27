module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_fstar_centralizer (D : Data G) {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Fstar (centralizer ({z} : Set G)) = pCoreOf 2 (centralizer ({z} : Set G)) :=
  TwelveEleven.fstar_eq_pCoreOf_of_charTwo
    (D.standing.charTwo _ (uc22p22f_isTwoLocal_centralizer hz1 hz2))

theorem c23_odd_relIndex_of_le (D : Data G) {H : Subgroup G} (hT : D.T ≤ H) :
    Odd (D.M.relIndex H) := by
  have h1 : D.M.relIndex H ∣ D.T.relIndex H := Subgroup.relIndex_dvd_of_le_left H D.sylowM.le
  have h2 : ¬ 2 ∣ D.T.relIndex H := (TwelveShort.isSylowIn_of_le D hT).2.2
  exact Nat.odd_iff.2 (by
    by_contra hc
    exact h2 (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (by omega)) h1))

theorem c23_seven_dvd_card_inf (D : Data G) (hx : DataExt D) (hsig : D.sig = {7})
    {H : Subgroup G} (hidx : (H ⊓ D.M).relIndex D.M = 49) : 7 ∣ Nat.card ↥(H ⊓ D.M) := by
  have h7 : (7 : ℕ) ∈ D.sig := by rw [hsig]; rfl
  obtain ⟨E, hEM, -, hEc⟩ := c23_exists_elemAbelian_card_pow (by norm_num : Nat.Prime 7)
    (M := D.M) (k := 3) (by
      rw [UC6.groupPRank_eq_pRank]
      exact hx.three_le 7 h7)
  have h1 : (7 : ℕ) ^ 3 ∣ Nat.card D.M := hEc ▸ Subgroup.card_dvd_of_le hEM
  have h2 := Subgroup.relIndex_mul_card H D.M
  rw [← Subgroup.inf_relIndex_right, hidx] at h2
  rw [← h2] at h1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
