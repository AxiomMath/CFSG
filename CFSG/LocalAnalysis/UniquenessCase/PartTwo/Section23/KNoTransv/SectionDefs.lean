module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Linear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OutcomeLocal

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

@[expose] def secP (X : Subgroup 𝔾) (a : M) : Submodule (ZMod 2) M :=
  Submodule.span (ZMod 2) {v | ∃ g ∈ X, v = (g : M →ₗ[ZMod 2] M) a}

@[expose] def secQ (X : Subgroup 𝔾) (φ : Module.Dual (ZMod 2) M) : Submodule (ZMod 2) M where
  carrier := {v | ∀ g ∈ X, φ ((g : M →ₗ[ZMod 2] M) v) = 0}
  add_mem' {u v} hu hv g hg := by rw [map_add, map_add, hu g hg, hv g hg, add_zero]
  zero_mem' g _ := by rw [map_zero, map_zero]
  smul_mem' c v hv g hg := by rw [map_smul, map_smul, hv g hg, smul_zero]

theorem le_stab_secP (X : Subgroup 𝔾) (a : M) : X ≤ i285_stab (secP X a) := by
  refine i285_le_stab fun g hg v hv => ?_
  exact Submodule.span_induction
    (fun w hw => by
      obtain ⟨h, hh, rfl⟩ := hw
      exact Submodule.subset_span ⟨g * h, X.mul_mem hg hh, (i285_mul_apply g h a).symm⟩)
    (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hv

theorem le_stab_secQ (X : Subgroup 𝔾) (φ : Module.Dual (ZMod 2) M) : X ≤ i285_stab (secQ X φ) := by
  refine i285_le_stab fun g hg v hv => ?_
  intro h hh
  rw [← i285_mul_apply h g v]
  exact hv (h * g) (X.mul_mem hh hg)

theorem conjClosure_le_triv_inf_fix (X : Subgroup 𝔾) {φ : Module.Dual (ZMod 2) M} {a : M}
    (hφa : φ a = 0) :
    conjClosure X (tv φ a hφa) ≤ i285_triv (secP X a) ⊓ i285_fix (secQ X φ) := by
  rw [conjClosure, Subgroup.closure_le]
  rintro x ⟨g, hg, rfl⟩
  have happ : ∀ v : M, (((g⁻¹ * tv φ a hφa * g : 𝔾)) : M →ₗ[ZMod 2] M) v =
      v + φ (((g : 𝔾) : M →ₗ[ZMod 2] M) v) • (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a) := by
    intro v
    rw [i285_mul_apply, i285_mul_apply, tv_apply, map_add, map_smul, i285_inv_apply_apply]
  constructor
  · refine (i285_mem_triv).2 ?_
    intro v
    rw [happ v, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, X.inv_mem hg, rfl⟩)
  · refine (i285_mem_fix).2 ?_
    intro v hv
    rw [happ v, hv g hg, zero_smul, add_zero]

@[expose] noncomputable def secRho (X : Subgroup 𝔾) (φ : Module.Dual (ZMod 2) M) (a : M) :
    ↥X →* LinearMap.GeneralLinearGroup (ZMod 2)
      (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype) :=
  i285_secHom (le_stab_secP X a) (le_stab_secQ X φ)

theorem pow_four_of_mem_ker_secRho {X : Subgroup 𝔾} {φ : Module.Dual (ZMod 2) M} {a : M}
    (hφa : φ a = 0) (hgen : X ≤ conjClosure X (tv φ a hφa)) {x : ↥X}
    (hx : x ∈ (secRho X φ a).ker) : x ^ 4 = 1 := by
  classical
  have hx1 : secRho X φ a x = 1 := MonoidHom.mem_ker.1 hx
  have hinf : (x : 𝔾) ∈ i285_triv (secP X a) ⊓ i285_fix (secQ X φ) :=
    conjClosure_le_triv_inf_fix X hφa (hgen x.2)
  have hP : ∀ v ∈ secP X a, ((x : 𝔾) : M →ₗ[ZMod 2] M) v - v ∈ secQ X φ := by
    intro v hv
    have h := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2)
        (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype) =>
        (f : (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype) →ₗ[ZMod 2]
          (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype))
          (Submodule.Quotient.mk ⟨v, hv⟩)) hx1
    rw [secRho, i285_secHom_mk] at h
    change _ = Submodule.Quotient.mk _ at h
    rw [Submodule.Quotient.eq] at h
    exact h
  have hU : (x : 𝔾) ∈ i285_U3 (secP X a) (secQ X φ) :=
    (i285_mem_U3).2 ⟨(i285_mem_triv).1 hinf.1, hP, (i285_mem_fix).1 hinf.2⟩
  exact Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact i285_pow_four hU)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
