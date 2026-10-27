module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem

private theorem ggWTT3_coxeterE6_eq :
    CoxeterMatrix.E₆ = coxeterMatrix (isFiniteType_cartan .E6) := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 :=
    CFSG.LieType.Chevalley.cartanE_eq 6
  exact (CFSG.StandardType.coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6)
    (hc.symm ▸ ggIntCartan_E₆)).symm

private theorem ggWTT3_isWeylMatrix_E6 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .E6)) := by
  rw [← ggWTT3_coxeterE6_eq]
  exact Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)

theorem ggWTT3_weylTypeW_of_e6ThreeModel
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hM : GGE6ThreeModelSCr R I) : GGTorusWeylTypeW 3 5 R I := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨Φ, T, w, h⟩ := (hM L' ψ hψ hker hperf A hAe hAI hr hsc).exists_data
  let Ψ : WeylGroup .E6 →* MulAut ↥A :=
    { toFun := h.weylAut
      map_one' := h.weylAut_one
      map_mul' := h.weylAut_mul }
  have hΨinj : Function.Injective Ψ := h.weylAut_injective
  have hΨrange : MonoidHom.range Ψ = Subgroup.closure (Set.range h.conjAut) := by
    apply le_antisymm
    · rintro x ⟨u, rfl⟩
      exact h.weylAut_mem u
    · rw [Subgroup.closure_le]
      rintro x ⟨i, rfl⟩
      exact ⟨simple .E6 i, by
        show h.weylAut (simple .E6 i) = h.conjAut i
        rw [h.weylAut_simple i]⟩
  have hrange : MonoidHom.range Ψ =
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    hΨrange.trans h.automizer_eq_reflGen.symm
  let f : WeylGroup .E6 ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hΨinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨Fin 6, coxeterMatrix (isFiniteType_cartan .E6), f,
    ggWTT3_isWeylMatrix_E6, ?_, ?_⟩
  · rw [← Nat.card_congr f.toEquiv, NoOffExc.card_weyl_E6]
    norm_num
  · intro i
    show h.weylAut (simple .E6 i) ∈ ggTorusReflSet 3 A
    rw [h.weylAut_simple i]
    exact h.conjAut_mem_ggTorusReflSet i

end CFSG.StandardType

end
