module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAuxQuot

public section

open CFSG.SignalizerFunctorTheorem Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.BAux

variable {H : Type*} [Group H] [Finite H]

theorem kOf_top_eq_oStar : kOf (⊤ : Subgroup H) = oStar H := by
  have h := oStar_map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
  exact h

theorem oStar_oStar_eq_top : oStar ↥(oStar H) = ⊤ := by
  rw [← kOf_eq_self_iff_oStar_eq_top]
  have := kOf_kOf (⊤ : Subgroup H)
  rwa [kOf_top_eq_oStar] at this

theorem oStar_mem_bSet : oStar H ∈ bSet H :=
  (kOf_eq_self_iff_oStar_eq_top (oStar H)).mpr oStar_oStar_eq_top

theorem perfectResidual_map_props {Z : Subgroup H} (hZ : oStar ↥Z = ⊤) :
    oStar ↥((CFSG.perfectResidual Z).map Z.subtype) = ⊤ ∧
      Group.IsPerfect ((CFSG.perfectResidual Z).map Z.subtype) ∧
      deg ↥((CFSG.perfectResidual Z).map Z.subtype) = deg ↥Z := by
  have e : ↥(CFSG.perfectResidual Z) ≃* ↥((CFSG.perfectResidual Z).map Z.subtype) :=
    Subgroup.equivMapOfInjective _ Z.subtype Z.subtype_injective
  have h1 : oStar ↥(CFSG.perfectResidual Z) = ⊤ := KAPI.oStar_eq_top_of_normal hZ _
  refine ⟨KAPI.oStar_eq_top_of_surjective h1 (f := e.toMonoidHom) e.surjective,
    isPerfect_perfectResidual_map Z, ?_⟩
  rw [← KAPI.deg_perfectResidual hZ]
  exact (KAPI.deg_congr e).symm

theorem deg_le_oStar_of_mem_bSet (hC : HypC H) {Z : Subgroup H} (hZ : Z ∈ bSet H) :
    deg ↥Z ≤ deg ↥(oStar H) := by
  have hZo : oStar ↥Z = ⊤ := (kOf_eq_self_iff_oStar_eq_top Z).mp hZ
  obtain ⟨hPo, hPp, hPd⟩ := perfectResidual_map_props hZo
  set P := (CFSG.perfectResidual Z).map Z.subtype with hP
  by_cases h : deg ↥(oStar H) ≤ deg ↥P
  · have hle : P ≤ oStar H := le_oStar_of_deg_le hC hPo hPp h
    have := KAPI.deg_le_of_injective hPo (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    omega
  · omega

end CFSG.SignalizerFunctorTheorem.McBride.Near.BAux
