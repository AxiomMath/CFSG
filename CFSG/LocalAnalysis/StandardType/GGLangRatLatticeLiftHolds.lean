module

public import CFSG.LocalAnalysis.StandardType.GGLangRatLift
public import CFSG.LocalAnalysis.StandardType.GGLangRatLatticeSurj
public import Certificates.Certificate13659
import CFSG.LocalAnalysis.StandardType.GGLangRatCentreSq
import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.Blueprint.ChevalleyRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped TensorProduct

private theorem langRatLL_rootChar_mul {τ : Tag} {L : Type} [Field L]
    (a b : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private noncomputable def langRatLL_val
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] (v : Fin τ.rank → ℤ) :
    TSc Ψ L →+ Additive Lˣ :=
  (AddMonoidHom.mk' (fun t : Additive (Fin τ.rank → Lˣ) =>
      Additive.ofMul (rootChar (Additive.toMul t) v)) (fun s t => by
        show Additive.ofMul (rootChar (Additive.toMul s * Additive.toMul t) v) = _
        rw [langRatLL_rootChar_mul]
        rfl)).comp (langRatPiT Ψ L).toAddMonoidHom

private theorem langRatLL_val_apply
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) {L : Type} [Field L] (v : Fin τ.rank → ℤ)
    (x : TSc Ψ L) :
    langRatLL_val Ψ L v x = Additive.ofMul (rootChar (Additive.toMul (langRatPiT Ψ L x)) v) :=
  rfl

theorem langRatSigmaT_rootChar
    {τ : Tag} {L : Type} [Field L] (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q : ℕ) (x : TSc Ψ L) (v : Fin τ.rank → ℤ) :
    rootChar (Additive.toMul (langRatPiT Ψ L (langRatSigmaT Ψ L w hw q x))) (w • v) =
      rootChar (Additive.toMul (langRatPiT Ψ L x)) v ^ q := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, toMul_zero]
    simp [rootChar]
  | tmul γ u =>
    have h1 : Additive.toMul (langRatPiT Ψ L (langRatSigmaT Ψ L w hw q (γ ⊗ₜ[ℤ] u))) =
        Hchar (τ := τ) (w • (γ : Fin τ.rank → ℤ)) (Additive.toMul u ^ q) := by
      rw [langRatSigmaT_tmul, toMul_langRatPiT_tmul]
      funext l
      show (Additive.toMul ((q : ℤ) • u)) ^ iform
          ((wRestrict Ψ w hw γ : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) (Pi.single l 1) = _
      rw [coe_wRestrict, toMul_zsmul, zpow_natCast]
      rfl
    have h2 : Additive.toMul (langRatPiT Ψ L (γ ⊗ₜ[ℤ] u)) =
        Hchar (τ := τ) (γ : Fin τ.rank → ℤ) (Additive.toMul u) := by
      rw [toMul_langRatPiT_tmul]
      rfl
    rw [h1, h2, rootChar_Hchar, rootChar_Hchar, iform_smul, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]
  | add x y hx hy =>
    simp only [map_add, toMul_add, langRatLL_rootChar_mul, hx, hy, mul_pow]

theorem langRatLatticeLift_holds :
    LangRatLatticeLift := by
  intro τ L _ _ _ p₀ S hτ w hn a b ha hb i hw
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  set Ψ := rationalRoots S.ρ (rootCharHom b) i with hΨ
  set m := componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) with hm
  have hroot : ∀ γ ∈ Ψ, IsRoot τ γ := fun γ hγ => isRoot_of_mem_rationalRoots S i hγ
  have hsurj : ∀ δ ∈ Ψ, ∃ γ ∈ Ψ, w • γ = δ := by
    have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset hroot
    have hbij : Set.BijOn (fun γ : Fin τ.rank → ℤ => w • γ) Ψ Ψ :=
      (hfin.injOn_iff_bijOn_of_mapsTo (f := fun γ : Fin τ.rank → ℤ => w • γ)
        (fun γ hγ => hw γ hγ)).1 (fun x _ y _ h => smul_left_cancel w h)
    intro δ hδ
    obtain ⟨γ, hγ, hγδ⟩ := hbij.surjOn hδ
    exact ⟨γ, hγ, hγδ⟩
  have hχ : ∀ γ ∈ Ψ, rootChar a (w • γ) = rootChar a γ ^ S.D.q := fun γ hγ => by
    rw [← S.rho_eq_smul hτ' hn (hroot γ hγ)]
    exact S.frob.rootChar_eq a ha γ (hroot γ hγ)
  obtain ⟨x₀, hx₀⟩ := langRatLift_exists_preimage Ψ (L := L) a
  have hx₀' : ∀ γ ∈ Ψ, langRatLL_val Ψ L γ x₀ = Additive.ofMul (rootChar a γ) := fun γ hγ => by
    rw [langRatLL_val_apply, hx₀ γ hγ]
  have hL2 : ∀ (x : TSc Ψ L) (v : Fin τ.rank → ℤ),
      langRatLL_val Ψ L (w • v) (langRatSigmaT Ψ L w hw S.D.q x) =
        S.D.q • langRatLL_val Ψ L v x := by
    intro x v
    rw [langRatLL_val_apply, langRatLL_val_apply, langRatSigmaT_rootChar, ofMul_pow]
  let K : AddSubgroup (TSc Ψ L) :=
    { carrier := {z | ∀ γ ∈ Ψ, langRatLL_val Ψ L γ z = 0}
      add_mem' := fun {x y} hx hy γ hγ => by rw [map_add, hx γ hγ, hy γ hγ, add_zero]
      zero_mem' := fun γ _ => map_zero _
      neg_mem' := fun {x} hx γ hγ => by rw [map_neg, hx γ hγ, neg_zero] }
  have hσK : ∀ z ∈ K, langRatSigmaT Ψ L w hw S.D.q z ∈ K := by
    intro z hz δ hδ
    obtain ⟨γ, hγ, rfl⟩ := hsurj δ hδ
    rw [hL2, hz γ hγ, smul_zero]
  have hKsq : ∀ z ∈ K,
      ((langRatSigmaT Ψ L w hw S.D.q : Module.End ℤ (TSc Ψ L)) ^ (2 * m)) z =
        (((S.D.q : ℤ) ^ m) ^ 2 : ℤ) • z := by
    intro z hz
    refine langRatCentreSq_holds τ L p₀ S hτ w hn b hb i hw z (fun γ hγ => ?_)
    have h := hz γ hγ
    rw [langRatLL_val_apply] at h
    exact Additive.ofMul.injective h
  have hax : langRatSigmaT Ψ L w hw S.D.q x₀ - x₀ ∈ K := by
    intro δ hδ
    obtain ⟨γ, hγ, rfl⟩ := hsurj δ hδ
    rw [map_sub, hL2, hx₀' γ hγ, hx₀' (w • γ) hδ, hχ γ hγ, ofMul_pow, sub_self]
  obtain ⟨k, hk, hkK⟩ := exists_sigma_fixed_lift (langRatSigmaT Ψ L w hw S.D.q) K hσK (2 * m)
    (((S.D.q : ℤ) ^ m) ^ 2) hKsq x₀ hax
  refine ⟨k, hk, fun γ hγ => ?_⟩
  have h1 : langRatLL_val Ψ L γ (k - ((((S.D.q : ℤ) ^ m) ^ 2 - 1)) • x₀) = 0 := hkK γ hγ
  rw [map_sub, map_zsmul, hx₀' γ hγ, sub_eq_zero, langRatLL_val_apply] at h1
  have h3 : rootChar (Additive.toMul (langRatPiT Ψ L k)) γ =
      rootChar a γ ^ ((((S.D.q : ℤ) ^ m) ^ 2 - 1) : ℤ) := by
    have h := congrArg Additive.toMul h1
    simpa [toMul_zsmul] using h
  have hQ : 1 ≤ (S.D.q ^ m) ^ 2 := Nat.one_le_pow _ _ (pow_pos S.hqpow.1.pos m)
  rw [h3, ← zpow_natCast]
  congr 1
  rw [Nat.cast_sub hQ]
  push_cast
  ring

end CFSG.StandardType.LangRat
