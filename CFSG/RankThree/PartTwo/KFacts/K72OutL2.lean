module

public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem isInnerAut_commutator_psl2 {K : Type*} [Field K] [Finite K]
    {P : Subgroup (MulAut (PSL2 K))} (hP : IsPGroup 3 P) {σ τ : MulAut (PSL2 K)} (hσ : σ ∈ P)
    (hτ : τ ∈ P) : IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  let ψ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom
  have hψ : ψ (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K (ψ σ) (ψ τ)]
    group
  obtain ⟨g, hg⟩ := mem_range_pglAction_of_rightHom_eq_one hψ
  obtain ⟨k, hk⟩ := hP ⟨_, mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)⟩
  have hk' : (σ * τ * σ⁻¹ * τ⁻¹) ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hg' : g ^ 3 ^ k = 1 := pglAction_injective (by rw [map_pow, hg, hk', map_one])
  obtain ⟨x, hx⟩ := exists_toPGL_eq_of_pow_odd (Odd.pow (by decide)) hg'
  exact ⟨x, by rw [← hg, ← hx, pglAction_toPGL]⟩

theorem isInnerAut_commutator_of_mulEquiv_psl2 {X : Type*} [Group X] {K : Type*} [Field K]
    [Finite K] (e : X ≃* PSL2 K) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) {σ τ : MulAut X}
    (hσ : σ ∈ P) (hτ : τ ∈ P) : IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  have h := isInnerAut_commutator_psl2 (hP.map (MulAut.congr e).toMonoidHom)
    (σ := MulAut.congr e σ) (τ := MulAut.congr e τ) ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
  rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, isInnerAut_congr] at h

end CFSG.RankThree.PartTwo.KFacts
