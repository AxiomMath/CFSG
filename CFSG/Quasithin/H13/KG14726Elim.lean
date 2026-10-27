module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Foundations.Basic

public noncomputable section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup
open scoped commutatorElement

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def quotientCenterCongr (e : X ≃* Y) : X ⧸ center X ≃* Y ⧸ center Y :=
  QuotientGroup.congr (center X) (center Y) e (map_center_eq e)

theorem ker_le_center_of_surjective (hX : CFSG.IsQuasisimple X) (ψ : X →* Y)
    (hψ : Function.Surjective ψ) [Nontrivial Y] : ψ.ker ≤ center X := by
  obtain ⟨hperf, hsimp, -⟩ := hX
  have : IsSimpleGroup (X ⧸ center X) := hsimp
  have hN : (ψ.ker.map (QuotientGroup.mk' (center X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hsup : ψ.ker ⊔ center X = ⊤ := by
      have := congrArg (comap (QuotientGroup.mk' (center X))) h
      rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at this
    set π := QuotientGroup.mk' ψ.ker with hπ
    have hmap : (center X).map π = ⊤ := by
      have h1 := congrArg (map π) hsup
      rwa [Subgroup.map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
        (Subgroup.map_eq_bot_iff _).mpr (by rw [hπ, QuotientGroup.ker_mk']), bot_sup_eq] at h1
    have hcomm : commutator X ≤ ψ.ker := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      have ha : π a ∈ center (X ⧸ ψ.ker) :=
        map_center_le_center (QuotientGroup.mk'_surjective _) (hmap ▸ mem_top (π a))
      rw [← QuotientGroup.ker_mk' ψ.ker, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp ha (π b)).symm
    have htop : ψ.ker = ⊤ := by
      rw [eq_top_iff, ← hperf.commutator_eq_top]
      exact hcomm
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hψ y
    exact hy ((MonoidHom.mem_ker).mp (htop ▸ mem_top x))

theorem comap_center_eq_of_perfect [Group.IsPerfect X] (ψ : X →* Y)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center X) :
    (center Y).comap ψ = center X := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap] at hx
    have hc : ∀ y : X, ⁅x, y⁆ ∈ center X := by
      intro y
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp hx (ψ y)).symm
    let d : X →* center X :=
      { toFun := fun y => ⟨⁅x, y⁆, hc y⟩
        map_one' := by ext; simp
        map_mul' := fun y₁ y₂ => by
          ext
          have h2 : ∀ g : X, g * (x * y₂ * x⁻¹ * y₂⁻¹) = x * y₂ * x⁻¹ * y₂⁻¹ * g := by
            simpa [commutatorElement_def] using mem_center_iff.mp (hc y₂)
          simp only [coe_mul, commutatorElement_def, mul_inv_rev]
          calc x * (y₁ * y₂) * x⁻¹ * (y₂⁻¹ * y₁⁻¹)
              = x * y₁ * x⁻¹ * ((x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
            _ = x * y₁ * x⁻¹ * y₁⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹) := by
              rw [← h2 y₁⁻¹]
              group }
    have hker' : d.ker = ⊤ := by
      rw [eq_top_iff, ← (Group.IsPerfect.commutator_eq_top (G := X))]
      exact Abelianization.commutator_subset_ker d
    rw [mem_center_iff]
    intro y
    have hy : y ∈ d.ker := hker' ▸ mem_top y
    rw [MonoidHom.mem_ker] at hy
    have h1 : ⁅x, y⁆ = 1 := congrArg Subtype.val hy
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · exact (map_le_iff_le_comap).mp (map_center_le_center hψ)

@[expose] def quotientCenterEquivOfSurjective (hX : CFSG.IsQuasisimple X) (ψ : X →* Y)
    (hψ : Function.Surjective ψ) [Nontrivial Y] : X ⧸ center X ≃* Y ⧸ center Y :=
  have : Group.IsPerfect X := hX.1
  have hker : center X = ((QuotientGroup.mk' (center Y)).comp ψ).ker := by
    rw [← comap_center_eq_of_perfect ψ hψ (ker_le_center_of_surjective hX ψ hψ)]
    ext x
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hψ))

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
@[expose] def quotientCenterSpecialLinearEquiv (n : ℕ) (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup (Fin n) F ⧸ center (Matrix.SpecialLinearGroup (Fin n) F) ≃*
      projectiveSL n F :=
  QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n F).symm

end CFSG.Quasithin.H13.KG14726

end
