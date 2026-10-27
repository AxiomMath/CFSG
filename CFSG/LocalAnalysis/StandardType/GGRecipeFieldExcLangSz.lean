module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import Certificates.Certificate113
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut
  szFieldAut_injective)

namespace RecipeExcLang

section Centerless

variable {M : Type} [Group M] {H : Subgroup M} (hZ : Subgroup.center H = ⊥)

include hZ in
theorem congr_symm_apply_mk (β : MulAut H) (h : H) :
    (MulAut.congr (centerQuotEquivOfBot hZ)).symm β (LargeEvenCenterMk H h) =
      LargeEvenCenterMk H (β h) := by
  rw [congr_centerQuotEquivOfBot_mk hZ, MulEquiv.apply_symm_apply]

end Centerless

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem ggRawFieldConj_suzuki (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGRawFieldConj p (LargeEvenCenterQuot (LargeEvenSzGroup a K)) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))) := by
  suffices key : ∀ H : Subgroup (GL (Fin 4) K), H = suzukiGroup a K →
      GGRawFieldConj p (LargeEvenCenterQuot H) (LargeEvenInnSet _)
        (LargeEvenMatFieldImage (LargeEvenCenterMk H)) from
    key _ (largeEvenSzGroup_eq a K)
  intro H hH
  subst hH
  intro _ _ u hu f hf huf hpow
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  set e := centerQuotEquivOfBot hZ with he
  set Ψ := MulAut.congr e with hΨ
  have hFΨ : ∀ φ ∈ LargeEvenMatFieldImage (LargeEvenCenterMk (suzukiGroup a K)),
      ∃ σ, Ψ φ = szFieldAut a K σ := by
    rintro φ ⟨σ, hG⟩
    refine ⟨σ, MulEquiv.ext fun h => ?_⟩
    have h1 := hG h (szFieldAut a K σ h) (coe_szFieldAut σ h)
    rw [hΨ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, he,
      centerQuotEquivOfBot_symm, h1, centerQuotEquivOfBot_mk]
  have hclos : Subgroup.closure (LargeEvenMatFieldImage (LargeEvenCenterMk (suzukiGroup a K))) ≤
      (szFieldAut a K).range.comap Ψ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro φ hφ
    obtain ⟨σ, hσ⟩ := hFΨ φ hφ
    exact ⟨σ, hσ.symm⟩
  obtain ⟨σ₀, -⟩ := hclos hf
  obtain ⟨x, rfl⟩ := hu
  set α := Ψ (MulAut.conj x * f) with hα
  have hαp : α ^ p = 1 := by rw [hα, ← map_pow, hpow, map_one]
  have hαinn : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) := by
    rintro ⟨y, hy⟩
    apply huf
    refine ⟨e.symm y, Ψ.injective ?_⟩
    rw [hΨ, mulAut_congr_conj, MulEquiv.apply_symm_apply]
    exact hy
  have hα1 : α ≠ 1 := fun h1 => hαinn ⟨1, by rw [map_one, h1]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨σ, h, -, -, -, -, hσp, -, -, hconj, -⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 α hord hαinn
  refine ⟨Ψ.symm (szFieldAut a K σ), ⟨σ, fun g g' hgg => ?_⟩, MulAut.conj (e.symm h⁻¹), ⟨_, rfl⟩,
    ?_, ?_⟩
  ·
    rw [hΨ, congr_symm_apply_mk hZ]
    congr 1
    exact Subtype.ext (Units.ext (by rw [coe_szFieldAut]; exact hgg.symm))
  ·
    rw [MulEquiv.orderOf_eq, orderOf_injective (szFieldAut a K) szFieldAut_injective, hσp]
  ·
    apply Ψ.injective
    have hu' : Ψ (MulAut.conj (e.symm h⁻¹)) = MulAut.conj h⁻¹ := by
      rw [hΨ, mulAut_congr_conj, MulEquiv.apply_symm_apply]
    have hR : Ψ (MulAut.conj (e.symm h⁻¹) * Ψ.symm (szFieldAut a K σ) *
        (MulAut.conj (e.symm h⁻¹))⁻¹) = MulAut.conj h⁻¹ * szFieldAut a K σ *
          (MulAut.conj h⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv Ψ (MulAut.conj (e.symm h⁻¹)), hu', MulEquiv.apply_symm_apply]
    rw [hR, ← hα, ← hconj, map_inv]
    group

end RecipeExcLang

open RecipeExcLang

theorem ggRawFieldConjOn_twB2 :
    GGRawFieldConjOn fun _ lab => lab.tag = .twB2 := by
  intro p hp hp2 lab hlab ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawFieldConj_suzuki (by omega) hK hp hp2⟩

end CFSG.StandardType
