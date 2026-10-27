module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Sixteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem bParam_le_of_fIndexSum_le (h416 : W4Lem4_16) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L T : Subgroup (MulAut W)} {Δ : Set (Subgroup (MulAut W))}
    {c : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y)
    (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y) (hfin : Δ.Finite)
    (hΔ : ∀ H ∈ Δ, H ≤ Y ∧ T ≤ H) (hgen : (⨆ H ∈ Δ, H) = Y)
    (hc : fIndexSum Δ ≤ (c : ℕ∞)) : bParam L Y ≤ c := by
  have hLY : L ≤ Y := le_sup_left.trans hLT.le
  have hTY : T ≤ Y := le_sup_right.trans hLT.le
  have hne : fIndexSum Δ ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top c) hc
  have hk : fIndexSum Δ = ((fIndexSum Δ).toNat : ℕ∞) := (ENat.coe_toNat hne).symm
  have hkc : (fIndexSum Δ).toNat ≤ c := by
    have h := hc
    rw [hk] at h
    exact_mod_cast h
  have ha : E3.aParam Y ≤ (fIndexSum Δ).toNat :=
    (h416 W hW Y L T Δ _ hLY hTY hLT hcomp hsyl hO2 hfin hΔ hgen hk).2 hfix
  exact bParam_le_aParam.trans (ha.trans hkc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
