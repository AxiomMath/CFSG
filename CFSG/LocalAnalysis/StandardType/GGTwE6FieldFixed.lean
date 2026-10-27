module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TwE6Transport


variable {K : Type} [Field K] [Finite K]

theorem fieldActor_mul_twConj (σ δ : K ≃+* K) (w : RecipeExcLang.twInndiagGroup K σ) :
    fieldActor (t := TwistTag.E6) σ δ * RecipeExcLang.twConj K σ w =
      RecipeExcLang.twConj K σ ⟨_, RecipeExcLang.entrywise_mem_twInndiag δ w.2⟩ *
        fieldActor σ δ := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change Units.map (entrywiseHom δ.toRingHom) ((w : ModGL TwistTag.E6.tag K) *
      (g : ModGL TwistTag.E6.tag K) * (w : ModGL TwistTag.E6.tag K)⁻¹) =
    Units.map (entrywiseHom δ.toRingHom) (w : ModGL TwistTag.E6.tag K) *
      Units.map (entrywiseHom δ.toRingHom) (g : ModGL TwistTag.E6.tag K) *
        (Units.map (entrywiseHom δ.toRingHom) (w : ModGL TwistTag.E6.tag K))⁻¹
  rw [map_mul, map_mul, map_inv]

theorem entrywise_eq_of_mem_recipeMat {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n) {R : Type*} [Group R]
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* R) {δ : K ≃+* K}
    {Y : Subgroup (MulAut R)}
    (hY : ∀ φ ∈ Y, φ * MulAut.congr ε (fieldActor σ δ) = MulAut.congr ε (fieldActor σ δ) * φ)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ recipeMat σ ε Y) :
    Units.map (entrywiseHom δ.toRingHom) x = x := by
  obtain ⟨w, hw, rfl⟩ := hx
  have hc : RecipeExcLang.twConj K σ w * fieldActor σ δ =
      fieldActor σ δ * RecipeExcLang.twConj K σ w :=
    (MulAut.congr ε).injective (by rw [map_mul, map_mul]; exact hY _ hw)
  rw [fieldActor_mul_twConj] at hc
  exact congrArg Subtype.val
    (NoOffTwE6Three.twConj_injective hn hK σ hσ (mul_right_cancel hc)).symm

end CFSG.StandardType.TwE6FieldCore

end
