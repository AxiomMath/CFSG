module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow

public section

namespace CFSG.StandardType.E6FieldFix

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem entrywise_inndiag_eq_of_commute
    (hK4 : 4 ≤ Nat.card K) (σ : K ≃+* K)
    (w : inndiagGroup τ K)
    (hc : inndiagConj τ K w * entrywiseAdjointAut τ σ =
      entrywiseAdjointAut τ σ * inndiagConj τ K w) :
    Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) = w := by
  have hw'mem : Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) ∈ inndiagGroup τ K :=
    entrywise_mem_inndiagGroup σ w.2
  have hzmem : (w : ModGL τ K)⁻¹ * Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) ∈
      inndiagGroup τ K :=
    mul_mem (inv_mem w.2) hw'mem
  have key : ∀ y : adjointGroup τ K,
      (w : ModGL τ K) * (y : ModGL τ K) * (w : ModGL τ K)⁻¹ =
        Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) * (y : ModGL τ K) *
          (Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K))⁻¹ := by
    intro y
    obtain ⟨x, rfl⟩ := (entrywiseAdjointAut τ σ).surjective y
    have h2 := congrArg (fun α : MulAut (adjointGroup τ K) => α x) hc
    simp only [MulAut.mul_apply] at h2
    have h3 := congrArg (fun g : adjointGroup τ K => (g : ModGL τ K)) h2
    simp only [coe_inndiagConj, coe_entrywiseAdjointAut, map_mul, map_inv] at h3
    have hxx : Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) =
        (entrywiseAdjointAut τ σ x : ModGL τ K) :=
      (coe_entrywiseAdjointAut τ σ x).symm
    rw [hxx] at h3
    exact h3
  have hcomm : ∀ h ∈ adjointGroup τ K,
      ((w : ModGL τ K)⁻¹ * Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K)) * h =
        h * ((w : ModGL τ K)⁻¹ *
          Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K)) := by
    intro h hh
    have hkey : (w : ModGL τ K) * h * (w : ModGL τ K)⁻¹ =
        Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) * h *
          (Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K))⁻¹ :=
      key ⟨h, hh⟩
    calc (w : ModGL τ K)⁻¹ * Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) * h
        = (w : ModGL τ K)⁻¹ *
            (Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) * h *
              (Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K))⁻¹) *
            Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) := by group
      _ = (w : ModGL τ K)⁻¹ * ((w : ModGL τ K) * h * (w : ModGL τ K)⁻¹) *
            Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) := by rw [← hkey]
      _ = h * ((w : ModGL τ K)⁻¹ *
            Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K)) := by group
  have hz := eq_one_of_commute_adjointGroup hK4 hzmem hcomm
  have hz1 : (w : ModGL τ K)⁻¹ * Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) = 1 :=
    hz
  calc Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K)
      = (w : ModGL τ K) * ((w : ModGL τ K)⁻¹ *
          Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K)) := by group
    _ = (w : ModGL τ K) * 1 := by rw [hz1]
    _ = (w : ModGL τ K) := by rw [mul_one]

end CFSG.StandardType.E6FieldFix

end
