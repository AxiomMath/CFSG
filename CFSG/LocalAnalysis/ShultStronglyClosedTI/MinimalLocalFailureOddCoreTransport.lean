module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem minimalLocalFailure_isolated_commutators_mem_oddCore {z : G}
    (hz : orderOf z = 2)
    (hisolated : ∀ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      g * z * g⁻¹ = z) :
    ∀ g : G, g * z * g⁻¹ * z⁻¹ ∈ oddCore G := by
  obtain ⟨A, hAgroup, hAfin, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} G
  let : Group A := hAgroup
  let : Fintype A := hAfin
  let f : A ≃* G := e.symm
  let t : A := f.symm z
  have ht1 : t ≠ 1 := by
    intro ht
    have hz1 : z = 1 := by
      simpa only [t, map_one, MulEquiv.apply_symm_apply] using congrArg f ht
    simp only [hz1, orderOf_one] at hz
    omega
  have ht2 : t * t = 1 := by
    apply f.injective
    simpa only [map_mul, map_one, t, MulEquiv.apply_symm_apply, pow_two] using
      (orderOf_eq_prime_iff.mp hz).1
  have htisolated : ∀ g : A, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t := by
    intro g hcomm
    apply f.injective
    simp only [map_mul, map_inv, t, MulEquiv.apply_symm_apply]
    apply hisolated (f g)
    simpa only [map_mul, map_inv, t, MulEquiv.apply_symm_apply] using congrArg f hcomm
  obtain ⟨N, hNnormal, hNodd, hN⟩ :=
    CFSG.ZStar.glauberman_zStar A t ht1 ht2 htisolated
  have hmapnormal : (N.map f.toMonoidHom).Normal :=
    hNnormal.map f.toMonoidHom f.surjective
  have hmapodd : Odd (Nat.card (N.map f.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact hNodd
  have hle : N.map f.toMonoidHom ≤ oddCore G := le_sSup ⟨hmapnormal, hmapodd⟩
  intro g
  have hmem := hle (Subgroup.mem_map_of_mem f.toMonoidHom (hN (f.symm g)))
  simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, t,
    MulEquiv.apply_symm_apply] using hmem

theorem minimalLocalFailure_isolated_image_central {z : G} (hz : orderOf z = 2)
    (hisolated : ∀ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      g * z * g⁻¹ = z) :
    QuotientGroup.mk' (oddCore G) z ∈ Subgroup.center (G ⧸ oddCore G) := by
  let f := QuotientGroup.mk' (oddCore G)
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (oddCore G) q
  have hker : f (g * z * g⁻¹ * z⁻¹) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [QuotientGroup.ker_mk']
    exact minimalLocalFailure_isolated_commutators_mem_oddCore hz hisolated g
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at hker
  have hcomm := congrArg (fun x => x * f g) hker
  simpa only [mul_assoc, inv_mul_cancel, mul_one, f] using hcomm

theorem minimalLocalFailure_odd_core_cover_image_central
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcover : H ⊔ oddCore G = ⊤) :
    QuotientGroup.mk' (oddCore G) z ∈ Subgroup.center (G ⧸ oddCore G) := by
  apply minimalLocalFailure_isolated_image_central h.distinguished_order
  intro g hcomm
  have hright : rightConjugateElem z g⁻¹ ∈ involutionPointClass z := ⟨g⁻¹, rfl⟩
  have hcommutes : Commute (rightConjugateElem z g⁻¹) z := by
    change (g⁻¹)⁻¹ * z * g⁻¹ * z = z * ((g⁻¹)⁻¹ * z * g⁻¹)
    simpa only [inv_inv] using hcomm
  simpa only [rightConjugateElem, inv_inv] using
    CFSG.ProperTwoGeneratedCore.local_point_isolated_of_odd_core_cover h hcover
      hright hcommutes

end CFSG.ShultStronglyClosedTI
