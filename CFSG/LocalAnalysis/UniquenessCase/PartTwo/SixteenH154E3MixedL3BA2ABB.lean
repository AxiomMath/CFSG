module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_e3_fixV_zpowers_inf_le_of_commSub_eq_bot {W : Type} [CommGroup W]
    {U : Subgroup W} {L : Subgroup (MulAut W)} {τ : MulAut W} (hτ2 : τ ^ 2 = 1)
    (h : commSub U (L.map (MulAut.conj τ).toMonoidHom) = ⊥) :
    (U ⊓ fixV (Subgroup.zpowers τ) : Subgroup W) ≤ U ⊓ fixV L := by
  have hττ : τ * τ = 1 := by rw [pow_two] at hτ2; exact hτ2
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left hττ
  have hfixLτ : U ≤ fixV (L.map (MulAut.conj τ).toMonoidHom) := commSub_eq_bot_iff.mp h
  intro u hu
  obtain ⟨huU, huF⟩ := hu
  refine ⟨huU, mem_fixV.mpr ?_⟩
  intro l hl
  have huτ : τ u = u := (mem_fixV.mp huF) τ (Subgroup.mem_zpowers τ)
  have hfix : (MulAut.conj τ l) u = u :=
    (mem_fixV.mp (hfixLτ huU)) _ ⟨l, hl, rfl⟩
  have hconj_eq : l * τ = τ * MulAut.conj τ l := by
    calc l * τ = τ * (τ⁻¹ * l * τ) := by group
      _ = τ * (τ * l * τ) := by rw [hτinv]
      _ = τ * MulAut.conj τ l := by rw [MulAut.conj_apply, hτinv]
  calc l u = (l * τ) u := by rw [MulAut.mul_apply, huτ]
    _ = (τ * MulAut.conj τ l) u := by rw [hconj_eq]
    _ = τ ((MulAut.conj τ l) u) := rfl
    _ = τ u := by rw [hfix]
    _ = u := huτ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
