module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.GroupTheory.FixedPointFree

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-point-free inversion below the distinguished maximal subgroup

This module packages the elementary endpoint used in Bender's Lemma 2.3(ii):
an involution normalizing a subgroup disjoint from `Hhat` acts on that
subgroup fixed-point-freely, because every fixed point centralizes `t` and
therefore lies in `H ≤ Hhat`.  A fixed-point-free involutory automorphism is
inversion.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Let `D` be normalized by the distinguished involution `t`.  If
`D ⊓ Hhat = ⊥`, then conjugation by `t` inverts every element of `D`.

No odd-order hypothesis is needed: fixed-point-free involutory
automorphisms are inversion and force odd order automatically. -/
public theorem involution_inverts_of_mem_normalizer_inf_Hhat_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (D : Subgroup G)
    (htN : c.t ∈ Subgroup.normalizer (D : Set G))
    (hD : D ⊓ c.Hhat = ⊥) :
    ∀ x : G, x ∈ D → c.t * x * c.t⁻¹ = x⁻¹ := by
  let tN : Subgroup.normalizer (D : Set G) := ⟨c.t, htN⟩
  let phi : MulAut D := D.normalizerMonoidHom tN
  have htt : c.t * c.t = 1 := by
    simpa [pow_two] using c.t_involution.2
  have htInvSelf : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right htt
  have hphiInvolutive : Function.Involutive phi := by
    intro y
    apply Subtype.ext
    simp only [phi, tN, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [htInvSelf]
    calc
      c.t * (c.t * (y : G) * c.t) * c.t =
          (c.t * c.t) * (y : G) * (c.t * c.t) := by group
      _ = (y : G) := by rw [htt]; simp
  have hphiFixedPointFree : MonoidHom.FixedPointFree phi := by
    intro y hyfix
    apply Subtype.ext
    have hyconj : c.t * (y : G) * c.t⁻¹ = (y : G) := by
      simpa [phi, tN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hyfix
    have hty : c.t * (y : G) = (y : G) * c.t := by
      have hmul := congrArg (fun z : G => z * c.t) hyconj
      simpa [mul_assoc] using hmul
    have hyH : (y : G) ∈ c.H := by
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact hty.symm
    have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hD]
      exact ⟨y.property, c.H_le_Hhat hyH⟩
    exact Subgroup.mem_bot.mp hybot
  intro x hx
  have hxinv := congrFun
    (hphiFixedPointFree.coe_eq_inv_of_involutive hphiInvolutive)
    (⟨x, hx⟩ : D)
  simpa [phi, tN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
    congrArg Subtype.val hxinv

end CFSG.GorensteinWalter
