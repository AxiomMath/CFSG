module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAut
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce

public section

namespace CFSG.StandardType

namespace NormalizerAut

theorem exists_injective_factor_of_surjective {L C G : Type*} [Group L] [Group C] [Group G]
    {π : L →* C} (hπ : Function.Surjective π) {ψ : L →* G} (hker : ψ.ker = π.ker) :
    ∃ χ : C →* G, Function.Injective χ ∧ χ.range = ψ.range ∧ ∀ y, χ (π y) = ψ y := by
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let χ : C →* G := (QuotientGroup.lift π.ker ψ hker.ge).comp e.symm.toMonoidHom
  have hval : ∀ y, χ (π y) = ψ y := by
    intro y
    have he : e.symm (π y) = QuotientGroup.mk y := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift π.ker ψ hker.ge (e.symm (π y)) = ψ y
    rw [he, QuotientGroup.lift_mk]
  refine ⟨χ, ?_, ?_, hval⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    obtain ⟨y, rfl⟩ := hπ c
    rw [MonoidHom.mem_ker, hval] at hc
    have hy : y ∈ π.ker := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hc
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.mp hy
  · ext g
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨y, rfl⟩ := hπ c
      exact ⟨y, (hval y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨π y, hval y⟩

theorem ggInduces_normAutOn {L C G : Type*} [Group L] [Group C] [Group G] {π : L →* C}
    {ψ : L →* G} (χ : C →* G) (hχ : Function.Injective χ) (hval : ∀ y, χ (π y) = ψ y)
    {M : Subgroup G} (hM : M ≤ Subgroup.normalizer (χ.range : Set G)) (g : M) :
    LayerSixE.GGInduces π ψ (g : G) (normAutOn χ hχ hM g) := by
  intro y y' h
  apply hχ
  rw [hval y', chi_normAutOn_apply, hval y]
  exact h

end NormalizerAut

end CFSG.StandardType
