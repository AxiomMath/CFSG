module

public import CFSG.RankThree.GF2n.Stroth80.SmithEightHolds

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

variable {K : Type} [Field K] {H : Type} [Group H] {φ : H →* GL (Fin 4 ⊕ Fin 4) K}
  {X : Type} [AddCommGroup X] [Module K X] {ρ : H →* (X ≃ₗ[K] X)}

theorem exists_statedOmega_factor (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hker : ∀ h : H, φ h = 1 → ρ h = 1) :
    ∃ ρ' : StatedOmega (StatedQuadPlus 4 K) →* (X ≃ₗ[K] X),
      ∀ (h : H) (hh : φ h ∈ StatedOmega (StatedQuadPlus 4 K)), ρ' ⟨φ h, hh⟩ = ρ h := by
  have hker' : φ.rangeRestrict.ker ≤ ρ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh ⊢
    exact hker h (by simpa using congrArg Subtype.val hh)
  let ρ₀ : φ.range →* (X ≃ₗ[K] X) :=
    MonoidHom.liftOfSurjective φ.rangeRestrict φ.rangeRestrict_surjective ⟨ρ, hker'⟩
  refine ⟨ρ₀.comp (MulEquiv.subgroupCongr hφ).symm.toMonoidHom, fun h hh => ?_⟩
  have h1 : ((MulEquiv.subgroupCongr hφ).symm ⟨φ h, hh⟩ : φ.range) = φ.rangeRestrict h := by
    ext
    simp
  change ρ₀ ((MulEquiv.subgroupCongr hφ).symm ⟨φ h, hh⟩) = ρ h
  rw [h1]
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ, hker'⟩ h

@[expose] noncomputable def repOm8
    (ρ' : StatedOmega (StatedQuadPlus 4 K) →* (X ≃ₗ[K] X))
    (A : StatedOmega (StatedQuadPlus 4 K)) :
    Representation K (CFSG.StandardType.Triality.Om8 K) X :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ρ'.comp (conjOm8 A).toMonoidHom)

theorem repOm8_apply (ρ' : StatedOmega (StatedQuadPlus 4 K) →* (X ≃ₗ[K] X))
    (A : StatedOmega (StatedQuadPlus 4 K)) (g : CFSG.StandardType.Triality.Om8 K) :
    repOm8 ρ' A g = (ρ' (conjOm8 A g) : X →ₗ[K] X) :=
  rfl

theorem repOm8_irreducible (ρ' : StatedOmega (StatedQuadPlus 4 K) →* (X ≃ₗ[K] X))
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hρ' : ∀ (h : H) (hh : φ h ∈ StatedOmega (StatedQuadPlus 4 K)), ρ' ⟨φ h, hh⟩ = ρ h)
    (hirr : ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : StatedOmega (StatedQuadPlus 4 K)) :
    ∀ S : Submodule K X,
      (∀ g, ∀ x ∈ S, repOm8 ρ' A g x ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS
  refine hirr S fun h x hx => ?_
  have hmem : φ h ∈ StatedOmega (StatedQuadPlus 4 K) :=
    hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩
  let g : CFSG.StandardType.Triality.Om8 K := (conjOm8 A).symm ⟨φ h, hmem⟩
  have hg : conjOm8 A g = ⟨φ h, hmem⟩ := (conjOm8 A).apply_symm_apply ⟨φ h, hmem⟩
  have h1 : ((ρ h : X ≃ₗ[K] X) : X →ₗ[K] X) = repOm8 ρ' A g := by
    rw [← hρ' h hmem, ← hg, repOm8_apply]
  rw [show ρ h x = repOm8 ρ' A g x from congrArg (fun f : X →ₗ[K] X => f x) h1]
  exact hS g x hx

theorem repOm8_nontrivial (ρ' : StatedOmega (StatedQuadPlus 4 K) →* (X ≃ₗ[K] X))
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hρ' : ∀ (h : H) (hh : φ h ∈ StatedOmega (StatedQuadPlus 4 K)), ρ' ⟨φ h, hh⟩ = ρ h)
    (hnt : ∃ h : H, ρ h ≠ 1) (A : StatedOmega (StatedQuadPlus 4 K)) :
    ∃ g, repOm8 ρ' A g ≠ 1 := by
  obtain ⟨h, hhne⟩ := hnt
  have hmem : φ h ∈ StatedOmega (StatedQuadPlus 4 K) :=
    hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩
  let g : CFSG.StandardType.Triality.Om8 K := (conjOm8 A).symm ⟨φ h, hmem⟩
  refine ⟨g, fun hcon => hhne ?_⟩
  have hg : conjOm8 A g = ⟨φ h, hmem⟩ := (conjOm8 A).apply_symm_apply ⟨φ h, hmem⟩
  have h2 : ((ρ' ⟨φ h, hmem⟩ : X ≃ₗ[K] X) : X →ₗ[K] X) = 1 := by
    rw [← hg, ← repOm8_apply]
    exact hcon
  rw [hρ' h hmem] at h2
  refine LinearEquiv.toLinearMap_injective ?_
  rw [LinearEquiv.coe_toLinearMap_one]
  simpa only [Module.End.one_eq_id] using h2

theorem repOm8_commute (ρ' : StatedOmega (StatedQuadPlus 4 K) →* (X ≃ₗ[K] X))
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hρ' : ∀ (h : H) (hh : φ h ∈ StatedOmega (StatedQuadPlus 4 K)), ρ' ⟨φ h, hh⟩ = ρ h)
    {T : X →ₗ[K] X}
    (hT : ∀ h : H, T ∘ₗ (ρ h : X →ₗ[K] X) = (ρ h : X →ₗ[K] X) ∘ₗ T)
    (A : StatedOmega (StatedQuadPlus 4 K)) (g : CFSG.StandardType.Triality.Om8 K) :
    T * repOm8 ρ' A g = repOm8 ρ' A g * T := by
  have hmem : (conjOm8 A g : GL (Fin 4 ⊕ Fin 4) K) ∈
      StatedOmega (StatedQuadPlus 4 K) := (conjOm8 A g).2
  have hmem' : (conjOm8 A g : GL (Fin 4 ⊕ Fin 4) K) ∈ φ.range := by
    rw [hφ]
    exact hmem
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp hmem'
  have h3 : (⟨φ h, hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩⟩ :
      StatedOmega (StatedQuadPlus 4 K)) = conjOm8 A g :=
    Subtype.ext hh
  have h1 : ((ρ h : X ≃ₗ[K] X) : X →ₗ[K] X) = repOm8 ρ' A g := by
    rw [← hρ' h (hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩), h3, repOm8_apply]
  rw [← h1]
  exact hT h

end CFSG.RankThree.GF2n.Stroth80
