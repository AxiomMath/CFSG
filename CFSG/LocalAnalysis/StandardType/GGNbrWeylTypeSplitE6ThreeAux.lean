module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem

private theorem ggWTSE6_coxeterE6_eq :
    coxeterMatrix (isFiniteType_cartan .E6) = CoxeterMatrix.E₆ := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
  exact coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6) (hc.symm ▸ ggIntCartan_E₆)

theorem ggWTSE6_isWeylMatrix_E6 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .E6)) := by
  rw [ggWTSE6_coxeterE6_eq]
  exact Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)

theorem ggWTSE6_weylTypeW_of_e6ThreeModel
    {R : Type} [Group R] {I : Set (MulAut R)} (hM : GGE6ThreeModelSCr R I) :
    GGTorusWeylTypeW 3 5 R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨Φ, T, w, h⟩ := (hM L' ψ hψ hker hperf A hAe hAI hr hsc).exists_data
  let Ψ : WeylGroup .E6 →* MulAut ↥A :=
    { toFun := h.weylAut
      map_one' := h.weylAut_one
      map_mul' := h.weylAut_mul }
  have hΨapply : ∀ u, Ψ u = h.weylAut u := fun _ => rfl
  have hrange_eq : MonoidHom.range Ψ =
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    apply le_antisymm
    · rintro x ⟨u, rfl⟩
      rw [h.automizer_eq_reflGen]
      exact h.weylAut_mem u
    · rw [h.automizer_eq_reflGen]
      refine (Subgroup.closure_le _).mpr ?_
      rw [Set.range_subset_iff]
      intro i
      exact ⟨simple .E6 i, by rw [hΨapply, h.weylAut_simple]⟩
  have hinj : Function.Injective Ψ := fun u v huv => h.weylAut_injective huv
  let e : WeylGroup .E6 ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange_eq)
  have he : ∀ u, (e u : MulAut ↥A) = h.weylAut u := fun _ => rfl
  refine ⟨Fin 6, coxeterMatrix (isFiniteType_cartan .E6), e,
    ggWTSE6_isWeylMatrix_E6, ?_, ?_⟩
  · have hcard : Nat.card ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 51840 := by
      rw [← Nat.card_congr e.toEquiv]
      exact NoOffExc.card_weyl_E6
    rw [hcard]
    norm_num
  · intro i
    change ((e (simple .E6 i) :
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) ∈ ggTorusReflSet 3 A
    rw [he, h.weylAut_simple i]
    exact h.conjAut_mem_ggTorusReflSet i

end CFSG.StandardType

end
