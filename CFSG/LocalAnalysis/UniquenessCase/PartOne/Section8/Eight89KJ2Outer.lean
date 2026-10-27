module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KJ2Basic
public import CFSG.GF2Type.Smith1979.CaseIIExclJ2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k91j2out_fixes_subgroup {J : Type} [Group J] (K : Subgroup J)
    (S : Subgroup (MulAut J)) (hN : ∀ k ∈ K, MulAut.conj k ∈ normalizer (S : Set (MulAut J)))
    (hT : S.comap (MulAut.conj : J →* MulAut J) = ⊥) : ∀ s ∈ S, ∀ k ∈ K, s k = k := by
  intro s hs k hk
  have h1 : MulAut.conj k * s⁻¹ * (MulAut.conj k)⁻¹ ∈ S :=
    (mem_normalizer_iff.mp (hN k hk) s⁻¹).mp (S.inv_mem hs)
  have h2 : MulAut.conj (s k * k⁻¹) ∈ S := by
    have := S.mul_mem hs h1
    rwa [← mul_assoc, ← mul_assoc, mulAut_mul_conj_mul_inv, ← map_inv, ← map_mul] at this
  have h3 : s k * k⁻¹ ∈ S.comap (MulAut.conj : J →* MulAut J) := h2
  rw [hT, mem_bot, mul_inv_eq_one] at h3
  exact h3

theorem j2AutCore_eq_bot_of_comap_eq_bot
    {J : Type} [Group J] [Finite J] (hJ : IsSpor J .J2)
    (K : Subgroup J) (hK : Nat.card K = 1080) (S : Subgroup (MulAut J)) (hS : IsPGroup 2 S)
    (hN : ∀ k ∈ K, MulAut.conj k ∈ normalizer (S : Set (MulAut J)))
    (hT : S.comap (MulAut.conj : J →* MulAut J) = ⊥) : S = ⊥ := by
  obtain ⟨eJ⟩ := id hJ
  have : Finite (MulAut J) :=
    Finite.of_injective (fun σ : MulAut J => σ.toEquiv) MulEquiv.toEquiv_injective
  have hfixK := k91j2out_fixes_subgroup K S hN hT
  by_contra hne
  have : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hne
  obtain ⟨⟨σ, hσS⟩, hσ⟩ := exists_orderOf_eq_two_of_isPGroup hS
  rw [Subgroup.orderOf_mk] at hσ
  have hσσ : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
  have hout : ∀ x : J, σ ≠ MulAut.conj x := by
    intro x hx
    have hxT : x ∈ S.comap (MulAut.conj : J →* MulAut J) := by
      show MulAut.conj x ∈ S
      rw [← hx]
      exact hσS
    rw [hT, mem_bot] at hxT
    rw [hxT, map_one] at hx
    rw [hx, orderOf_one] at hσ
    omega
  have h336 := CFSG.GF2Type.Smith1979.Case2.card_fixedPoints_outer_of_mulEquiv
    (eJ.trans (CFSG.ComponentClassification.J2Cover.nativeEquivP :
      CFSG.Blueprint.NativeSporadic.Carrier .J2 ≃* _)) σ hσσ hout
  have hinj : Function.Injective
      (fun k : K => (⟨k.1, hfixK σ hσS k.1 k.2⟩ : {x : J // σ x = x})) :=
    fun a b hab => Subtype.ext (by simpa using hab)
  have := Nat.card_le_card_of_injective _ hinj
  rw [hK, h336] at this
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
