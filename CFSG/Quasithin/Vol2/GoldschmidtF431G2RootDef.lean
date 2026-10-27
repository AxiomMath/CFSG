module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

abbrev C (K : Type) [Field K] : Type := ↥(adjointGroup Tag.G2 K)

@[expose] def rNA : Fin Tag.G2.rank → ℤ := ![-1, 0]

section Elements

variable {K : Type} [Field K]

@[expose] noncomputable def xe (γ : Fin Tag.G2.rank → ℤ) (s : K) : C K :=
  ⟨gX γ s, pinnedX_mem_adjointGroup (τ := Tag.G2) γ s⟩

theorem xe_add (γ : Fin Tag.G2.rank → ℤ) (s t : K) : xe γ (s + t) = xe γ s * xe γ t :=
  Subtype.ext (gX_add γ s t)

theorem xe_zero (γ : Fin Tag.G2.rank → ℤ) : xe γ (0 : K) = 1 :=
  Subtype.ext (gX_zero γ)

theorem xe_injective (γ : Fin Tag.G2.rank → ℤ) : Function.Injective (xe (K := K) γ) :=
  fun _ _ h => pinnedX_injective Tag.G2 K γ (congrArg Subtype.val h)

theorem xe_eq_one_iff (γ : Fin Tag.G2.rank → ℤ) {s : K} : xe γ s = 1 ↔ s = 0 :=
  ⟨fun h => xe_injective γ (h.trans (xe_zero γ).symm), fun h => h ▸ xe_zero γ⟩

theorem xe_inv_neg (γ : Fin Tag.G2.rank → ℤ) (s : K) : (xe γ s)⁻¹ = xe γ (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← xe_add, add_neg_cancel, xe_zero])

theorem xe_mul_self [CharP K 2] (γ : Fin Tag.G2.rank → ℤ) (s : K) : xe γ s * xe γ s = 1 := by
  rw [← xe_add, CharTwo.add_self_eq_zero, xe_zero]

theorem xe_inv [CharP K 2] (γ : Fin Tag.G2.rank → ℤ) (s : K) : (xe γ s)⁻¹ = xe γ s :=
  inv_eq_of_mul_eq_one_right (xe_mul_self γ s)

@[expose] def xa (s : K) : C K := xe rA s

theorem coe_xa (s : K) : ((xa s : C K) : ModGL Tag.G2 K) = gX rA s := rfl

theorem xa_add (s t : K) : xa (s + t) = xa s * xa t := xe_add rA s t

theorem xa_zero : xa (0 : K) = 1 := xe_zero rA

theorem xa_eq_one_iff {s : K} : xa s = 1 ↔ s = 0 := xe_eq_one_iff rA

theorem xa_mul_self [CharP K 2] (s : K) : xa s * xa s = 1 := xe_mul_self rA s

theorem xa_inv [CharP K 2] (s : K) : (xa s)⁻¹ = xa s := xe_inv rA s

@[expose] def xr (s : K) : C K := xe rR s

theorem coe_xr (s : K) : ((xr s : C K) : ModGL Tag.G2 K) = gX rR s := rfl

theorem xr_add (s t : K) : xr (s + t) = xr s * xr t := xe_add rR s t

theorem xr_zero : xr (0 : K) = 1 := xe_zero rR

theorem xr_mul_self [CharP K 2] (s : K) : xr s * xr s = 1 := xe_mul_self rR s

theorem xr_inv [CharP K 2] (s : K) : (xr s)⁻¹ = xr s := xe_inv rR s

@[expose] def xu (s : K) : C K := xe rU s

theorem coe_xu (s : K) : ((xu s : C K) : ModGL Tag.G2 K) = gX rU s := rfl

theorem xu_add (s t : K) : xu (s + t) = xu s * xu t := xe_add rU s t

theorem xu_zero : xu (0 : K) = 1 := xe_zero rU

theorem xu_eq_one_iff {s : K} : xu s = 1 ↔ s = 0 := xe_eq_one_iff rU

theorem xu_mul_self [CharP K 2] (s : K) : xu s * xu s = 1 := xe_mul_self rU s

theorem xu_inv [CharP K 2] (s : K) : (xu s)⁻¹ = xu s := xe_inv rU s

@[expose] def xv (s : K) : C K := xe rV s

theorem coe_xv (s : K) : ((xv s : C K) : ModGL Tag.G2 K) = gX rV s := rfl

theorem xv_add (s t : K) : xv (s + t) = xv s * xv t := xe_add rV s t

theorem xv_zero : xv (0 : K) = 1 := xe_zero rV

theorem xv_eq_one_iff {s : K} : xv s = 1 ↔ s = 0 := xe_eq_one_iff rV

theorem xv_mul_self [CharP K 2] (s : K) : xv s * xv s = 1 := xe_mul_self rV s

theorem xv_inv [CharP K 2] (s : K) : (xv s)⁻¹ = xv s := xe_inv rV s

@[expose] def xb (s : K) : C K := xe rB s

theorem coe_xb (s : K) : ((xb s : C K) : ModGL Tag.G2 K) = gX rB s := rfl

theorem xb_add (s t : K) : xb (s + t) = xb s * xb t := xe_add rB s t

theorem xb_zero : xb (0 : K) = 1 := xe_zero rB

theorem xb_eq_one_iff {s : K} : xb s = 1 ↔ s = 0 := xe_eq_one_iff rB

theorem xb_mul_self [CharP K 2] (s : K) : xb s * xb s = 1 := xe_mul_self rB s

theorem xb_inv [CharP K 2] (s : K) : (xb s)⁻¹ = xb s := xe_inv rB s

@[expose] def xc (s : K) : C K := xe rC s

theorem coe_xc (s : K) : ((xc s : C K) : ModGL Tag.G2 K) = gX rC s := rfl

theorem xc_add (s t : K) : xc (s + t) = xc s * xc t := xe_add rC s t

theorem xc_zero : xc (0 : K) = 1 := xe_zero rC

theorem xc_injective : Function.Injective (xc (K := K)) := xe_injective rC

theorem xc_eq_one_iff {s : K} : xc s = 1 ↔ s = 0 := xe_eq_one_iff rC

theorem xc_mul_self [CharP K 2] (s : K) : xc s * xc s = 1 := xe_mul_self rC s

theorem xc_inv [CharP K 2] (s : K) : (xc s)⁻¹ = xc s := xe_inv rC s

@[expose] def xna (s : K) : C K := xe rNA s

@[expose] def xnr (s : K) : C K := xe rNR s

theorem xnr_mul_self [CharP K 2] (s : K) : xnr s * xnr s = 1 := xe_mul_self rNR s

theorem xnr_inv [CharP K 2] (s : K) : (xnr s)⁻¹ = xnr s := xe_inv rNR s

end Elements

end CFSG.Quasithin.H13.F431.G2
