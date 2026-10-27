module

public import CFSG.Quasithin.Background.G8Lambda
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem isSubnormal_top_of_isSubnormal_generalizedFitting {X : Subgroup H}
    (hX : IsSubnormal X (CFSG.generalizedFitting H)) : IsSubnormal X ⊤ := by
  have hF : (CFSG.generalizedFitting H).Normal := by
    rw [CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal H
  have hFtop : ((CFSG.generalizedFitting H).subgroupOf ⊤).Normal := hF.subgroupOf ⊤
  exact A4.subnormal_trans hX (A4.subnormal_of_normal le_top hFtop)

theorem layer_le_of_lambda_le {X : Subgroup H}
    (hΛ : lambdaSubgroup (Subgroup.centralizer (X : Set H) ⊓ CFSG.generalizedFitting H) ≤ X)
    (hX : IsSubnormal X (CFSG.generalizedFitting H)) : CFSG.layer H ≤ X := by
  have hXH : IsSubnormal X ⊤ := isSubnormal_top_of_isSubnormal_generalizedFitting hX
  refine sSup_le fun K hK => ?_
  have hKo : IsComponentOf K ⊤ := (CFSG.isComponent_iff_open K).mp hK
  have hKE : K ≤ CFSG.generalizedFitting H := le_sup_of_le_right (le_sSup hK)
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes K X hKo hXH
    with hle | hcomm
  · exact hle
  · have hKC : K ≤ Subgroup.centralizer (X : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hΛK : lambdaSubgroup K = K := lambdaSubgroup_eq_of_isQuasisimple hKo.2.2
    rw [← hΛK]
    exact (lambdaSubgroup_mono (le_inf hKC hKE)).trans hΛ

theorem g8_9_two (hO2 : CFSG.pCore 2 H = ⊥) {θ : Subgroup H} (hθ : IsTheta H θ) {U : Subgroup H}
    (hU : IsPGroup 2 U) : U ⊓ Subgroup.centralizer (θ : Set H) = ⊥ := by
  have := hθ.normal
  exact G8.g8_9_core hO2 hθ.le_generalizedFitting hθ.layer_le hθ.lambda_le hU
    Subgroup.le_normalizer_of_normal

theorem g8_9_one (hO2 : CFSG.pCore 2 H = ⊥) {X : Subgroup H}
    (hΛ : lambdaSubgroup (Subgroup.centralizer (X : Set H) ⊓ CFSG.generalizedFitting H) ≤ X)
    (hX : IsSubnormal X (CFSG.generalizedFitting H)) {U : Subgroup H} (hU : IsPGroup 2 U)
    (hUX : U ≤ Subgroup.normalizer (X : Set H)) : U ⊓ Subgroup.centralizer (X : Set H) = ⊥ := by
  have hXF : X ≤ CFSG.generalizedFitting H := A4.subnormal_le hX
  have hEX : CFSG.layer H ≤ X := layer_le_of_lambda_le hΛ hX
  have hFF : CFSG.fittingSubgroup H ≤ CFSG.generalizedFitting H := le_sup_left
  have hsub : CFSG.fittingSubgroup H ⊓ Subgroup.centralizer (X : Set H) ≤
      Subgroup.centralizer (X : Set H) ⊓ CFSG.generalizedFitting H :=
    fun x hx => ⟨hx.2, hFF hx.1⟩
  exact G8.g8_9_core hO2 hXF hEX ((lambdaSubgroup_mono hsub).trans hΛ) hU hUX

end CFSG.Quasithin
