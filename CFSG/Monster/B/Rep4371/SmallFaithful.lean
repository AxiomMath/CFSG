
module

public import CFSG.Monster.B.Rep4371.SmallFaithfulBase

public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.OddDegree.Main
public import CFSG.Monster.B.Gen.GenerationBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Rep4371
open scoped Matrix

instance isSimpleGroup_Cbar :

    IsSimpleGroup Cbar := short_centralizer_generated_quotient_simple.2.2.1

theorem chiMat_injective :
    Function.Injective chiMat := by
  refine (Units.map_injective (f := (matR : Module.End ℚ Vst →* Matrix (Fin 4371) (Fin 4371) ℚ))
    matR.injective).comp ?_
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ Vst).symm.injective.comp chi_injective

theorem Cbar_nonabelian : ∃ a b : Cbar, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := Ebar_nonabelian
  exact ⟨a, b, fun h => hab (Subtype.ext h)⟩

theorem short_centralizer_small_faithful_representations :
    Module.finrank ℚ Vst = 4371 ∧
    (∀ (g : Cgen) (v : Vst), ((chi (kappa g) v : Vst) : SpaceB) = (g : SpaceB ≃ₗ[ℚ] SpaceB) v) ∧
    Function.Injective chi ∧
    LinearMap.trace ℚ Vst (chi xbar : Vst →ₗ[ℚ] Vst) = 275 ∧
    (∃ d, 1 ≤ d ∧ d ≤ 4370 ∧ ∃ σ : Cbar →* GL (Fin d) (ZMod 2), Function.Injective σ ∧
      ∀ Y : Submodule (ZMod 2) (Fin d → ZMod 2),
        (∀ g, ∀ y ∈ Y, ((σ g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ y ∈ Y) →
          Y = ⊥ ∨ Y = ⊤) ∧
    ∃ τ : Cbar →* GL (Fin 4370) (ZMod 2), Function.Injective τ := by
  have hne : chiMat ≠ 1 := by
    intro h
    obtain ⟨a, b, hab⟩ := Cbar_nonabelian
    apply hab
    apply chiMat_injective
    rw [h]
    rfl
  obtain ⟨h1, h2⟩ := OddDegree.simple_odd_rational_degree_binary_bound Cbar_nonabelian
    (n := 4371) (by norm_num) (by decide) chiMat hne
  exact ⟨finrank_Vst, coe_chi_kappa_apply, chi_injective, trace_chi_xbar, h1, h2⟩

end CFSG.Monster.B
