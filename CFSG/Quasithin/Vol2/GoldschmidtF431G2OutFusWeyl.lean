module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFusChain
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ClsRoot

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Weyl

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] def nW (i : Fin Tag.G2.rank) : C K := ⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩

variable (K) in
@[expose] def dT (i : Fin Tag.G2.rank) (t : Kˣ) : C K :=
  ⟨torusElt Tag.G2 K i t, torusElt_mem_adjointGroup i t⟩

theorem dT_mem_torusSub (i : Fin Tag.G2.rank) (t : Kˣ) : dT K i t ∈ torusSub Tag.G2 K :=
  Subgroup.mem_subgroupOf.2 (torusElt_mem_torusGroup i t)

theorem nW_conj_xe (i : Fin Tag.G2.rank) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (s : K) :
    nW K i * xe γ s * (nW K i)⁻¹ = xe (reflect Tag.G2 i γ) s :=
  Subtype.ext (Cls.weylElt_conj_pinnedX i hγ s)

theorem reflect_r_v : reflect .G2 Cls.iR ![1, 2] = ![1, 1] :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_r_c : reflect .G2 Cls.iR ![2, 3] = ![2, 3] :=
  List.ofFn_injective (by decide +kernel)

theorem nA_xr (s : K) : nW K Cls.iA * xr s * (nW K Cls.iA)⁻¹ = xu s := by
  have h := nW_conj_xe (K := K) Cls.iA Cls.isRoot_r s
  rw [Cls.reflect_a_r] at h
  exact h

theorem nR_xa (s : K) : nW K Cls.iR * xa s * (nW K Cls.iR)⁻¹ = xb s := by
  have h := nW_conj_xe (K := K) Cls.iR Cls.isRoot_a s
  rw [Cls.reflect_r_a] at h
  exact h

theorem nR_xv (s : K) : nW K Cls.iR * xv s * (nW K Cls.iR)⁻¹ = xu s := by
  have h := nW_conj_xe (K := K) Cls.iR Cls.isRoot_v s
  rw [reflect_r_v] at h
  exact h

theorem nR_xc (s : K) : nW K Cls.iR * xc s * (nW K Cls.iR)⁻¹ = xc s := by
  have h := nW_conj_xe (K := K) Cls.iR Cls.isRoot_c s
  rw [reflect_r_c] at h
  exact h

theorem nR_nf (α ν γ : K) :
    nW K Cls.iR * nf α 0 0 ν 0 γ * (nW K Cls.iR)⁻¹ = nf 0 0 ν 0 α γ := by
  have h : nf α 0 0 ν 0 γ = xa α * xv ν * xc γ := by
    simp [nf, xr_zero, xu_zero, xb_zero]
  have e : ∀ x y z : C K, nW K Cls.iR * (x * y * z) * (nW K Cls.iR)⁻¹ =
      (nW K Cls.iR * x * (nW K Cls.iR)⁻¹) * (nW K Cls.iR * y * (nW K Cls.iR)⁻¹) *
        (nW K Cls.iR * z * (nW K Cls.iR)⁻¹) := fun x y z => by group
  rw [h, e, nR_xa, nR_xv, nR_xc, ← (cc_ub ν α).eq]
  simp [nf, xa_zero, xr_zero, xv_zero]

theorem dT_conj_xe (i : Fin Tag.G2.rank) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (t : Kˣ)
    (s : K) :
    dT K i t * xe γ s * (dT K i t)⁻¹ =
      xe γ (((t ^ (∑ j, Tag.G2.cartan i j * γ j) : Kˣ) : K) * s) :=
  Subtype.ext (root_torus_conjugation i hγ t s)

theorem dT_xu (t : Kˣ) (s : K) : dT K Cls.iA t * xu s * (dT K Cls.iA t)⁻¹ = xu ((t : K) * s) := by
  have h := dT_conj_xe (K := K) Cls.iA Cls.isRoot_u t s
  rwa [show (∑ j, Tag.G2.cartan Cls.iA j * (![1, 1] : Fin Tag.G2.rank → ℤ) j) = 1 by decide,
    zpow_one] at h

theorem dT_xv (t : Kˣ) (s : K) : dT K Cls.iR t * xv s * (dT K Cls.iR t)⁻¹ = xv ((t : K) * s) := by
  have h := dT_conj_xe (K := K) Cls.iR Cls.isRoot_v t s
  rwa [show (∑ j, Tag.G2.cartan Cls.iR j * (![1, 2] : Fin Tag.G2.rank → ℤ) j) = 1 by decide,
    zpow_one] at h

theorem dT_xc (t : Kˣ) (s : K) : dT K Cls.iA t * xc s * (dT K Cls.iA t)⁻¹ = xc ((t : K) * s) := by
  have h := dT_conj_xe (K := K) Cls.iA Cls.isRoot_c t s
  rwa [show (∑ j, Tag.G2.cartan Cls.iA j * (![2, 3] : Fin Tag.G2.rank → ℤ) j) = 1 by decide,
    zpow_one] at h

theorem dT_xb (t : Kˣ) (s : K) :
    dT K Cls.iA t * xb s * (dT K Cls.iA t)⁻¹ = xb ((t : K)⁻¹ * s) := by
  have h := dT_conj_xe (K := K) Cls.iA Cls.isRoot_b t s
  rwa [show (∑ j, Tag.G2.cartan Cls.iA j * (![1, 3] : Fin Tag.G2.rank → ℤ) j) = -1 by decide,
    zpow_neg_one, Units.val_inv_eq_inv_val] at h

theorem dT_xa (t : Kˣ) (s : K) :
    dT K Cls.iA t * xa s * (dT K Cls.iA t)⁻¹ = xa ((t : K) ^ 2 * s) := by
  have h := dT_conj_xe (K := K) Cls.iA Cls.isRoot_a t s
  rwa [show (∑ j, Tag.G2.cartan Cls.iA j * (![1, 0] : Fin Tag.G2.rank → ℤ) j) = 2 by decide,
    zpow_two, Units.val_mul, ← pow_two] at h

theorem torus_xu {μ : K} (hμ : μ ≠ 0) :
    ∃ g ∈ torusSub Tag.G2 K, g * xu μ * g⁻¹ = xu 1 := by
  refine ⟨dT K Cls.iA (Units.mk0 μ⁻¹ (inv_ne_zero hμ)), dT_mem_torusSub _ _, ?_⟩
  rw [dT_xu, Units.val_mk0, inv_mul_cancel₀ hμ]

theorem torus_xv {ν : K} (hν : ν ≠ 0) :
    ∃ g ∈ torusSub Tag.G2 K, g * xv ν * g⁻¹ = xv 1 := by
  refine ⟨dT K Cls.iR (Units.mk0 ν⁻¹ (inv_ne_zero hν)), dT_mem_torusSub _ _, ?_⟩
  rw [dT_xv, Units.val_mk0, inv_mul_cancel₀ hν]

theorem torus_xc {γ : K} (hγ : γ ≠ 0) :
    ∃ g ∈ torusSub Tag.G2 K, g * xc γ * g⁻¹ = xc 1 := by
  refine ⟨dT K Cls.iA (Units.mk0 γ⁻¹ (inv_ne_zero hγ)), dT_mem_torusSub _ _, ?_⟩
  rw [dT_xc, Units.val_mk0, inv_mul_cancel₀ hγ]

theorem torus_xb {β : K} (hβ : β ≠ 0) :
    ∃ g ∈ torusSub Tag.G2 K, g * xb β * g⁻¹ = xb 1 := by
  refine ⟨dT K Cls.iA (Units.mk0 β hβ), dT_mem_torusSub _ _, ?_⟩
  rw [dT_xb, Units.val_mk0, inv_mul_cancel₀ hβ]

theorem torus_xa [Finite K] {α : K} (hα : α ≠ 0) :
    ∃ g ∈ torusSub Tag.G2 K, g * xa α * g⁻¹ = xa 1 := by
  obtain ⟨s, hs⟩ := exists_sq_eq α⁻¹
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply inv_ne_zero hα
    rw [← hs]
    ring
  refine ⟨dT K Cls.iA (Units.mk0 s hs0), dT_mem_torusSub _ _, ?_⟩
  rw [dT_xa, Units.val_mk0, hs, inv_mul_cancel₀ hα]

end Weyl

end CFSG.Quasithin.H13.F431.G2
