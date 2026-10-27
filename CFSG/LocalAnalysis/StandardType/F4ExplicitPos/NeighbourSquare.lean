module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicImplementersPart2

@[expose] public section

public section

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType

open CFSG.StandardType.S2MathFi1035Pos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.LieType.Universal.Symplectic CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open

namespace CFSG.StandardType.F4ExplicitPos.NeighbourSquare

section GenericSquare

variable {B C : Type*} [Group B] [Group C]

theorem map_conj_map_conj_eq_of_conj_eq_on_range
    (Φ : B →* C) {U : Subgroup B} {ze w : C} {v : B}
    (h : ∀ y ∈ Φ.range, (ze⁻¹ * w) * y * (ze⁻¹ * w)⁻¹ = Φ v * y * (Φ v)⁻¹) :
    ((U.map (MulAut.conj v).toMonoidHom).map Φ).map
        (MulAut.conj ze).toMonoidHom =
      (U.map Φ).map (MulAut.conj w).toMonoidHom := by
  have hmap_conj : (U.map (MulAut.conj v).toMonoidHom).map Φ =
      (U.map Φ).map (MulAut.conj (Φ v)).toMonoidHom := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨Φ u, Subgroup.mem_map.2 ⟨u, hu, rfl⟩, by
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv]⟩
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨v * u * v⁻¹, Subgroup.mem_map.2 ⟨u, hu, by simp [MulAut.conj_apply]⟩, by
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv]⟩
  rw [hmap_conj, Subgroup.map_conj_map_conj]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    have hh := h (Φ u) (MonoidHom.mem_range.2 ⟨u, rfl⟩)
    refine ⟨Φ u, Subgroup.mem_map.2 ⟨u, hu, rfl⟩, ?_⟩
    calc w * Φ u * w⁻¹
        = ze * ((ze⁻¹ * w) * Φ u * (ze⁻¹ * w)⁻¹) * ze⁻¹ := by group
      _ = ze * (Φ v * Φ u * (Φ v)⁻¹) * ze⁻¹ := by rw [hh]
      _ = (ze * Φ v) * Φ u * (ze * Φ v)⁻¹ := by group
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    have hh := h (Φ u) (MonoidHom.mem_range.2 ⟨u, rfl⟩)
    refine ⟨Φ u, Subgroup.mem_map.2 ⟨u, hu, rfl⟩, ?_⟩
    calc (ze * Φ v) * Φ u * (ze * Φ v)⁻¹
        = ze * (Φ v * Φ u * (Φ v)⁻¹) * ze⁻¹ := by group
      _ = ze * ((ze⁻¹ * w) * Φ u * (ze⁻¹ * w)⁻¹) * ze⁻¹ := by rw [← hh]
      _ = w * Φ u * w⁻¹ := by group

end GenericSquare

section ActualNeighbour

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem exists_vOmega_implementing_untwist
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Ωˣ}
    (j : KernelComponent χ)
    {Φ : StatedSp 3 Ω →* ModGL Tag.F4 Ω}
    (hΦrange : Φ.range = componentRootSpan Ω χ j)
    {ze w : ModGL Tag.F4 Ω}
    (hw : ze⁻¹ * w ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)) :
    ∃ vΩ : StatedSp 3 Ω, ∀ y ∈ componentRootSpan Ω χ j,
      (ze⁻¹ * w) * y * (ze⁻¹ * w)⁻¹ = Φ vΩ * y * (Φ vΩ)⁻¹ := by
  obtain ⟨k, hk, hkconj⟩ :=
    CyclicImplementers.exists_mem_componentRootSpan_conj_eq_of_mem_Z_good
      (L := Ω) j hw
  have hkrange : k ∈ Φ.range := by rw [hΦrange]; exact hk
  obtain ⟨vΩ, hvΩ⟩ := MonoidHom.mem_range.1 hkrange
  refine ⟨vΩ, fun y hy => ?_⟩
  rw [hkconj y hy, hvΩ]

theorem exists_vOmega_neighbour_square_allU
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Ωˣ}
    (j : KernelComponent χ)
    {Φ : StatedSp 3 Ω →* ModGL Tag.F4 Ω}
    (hΦrange : Φ.range = componentRootSpan Ω χ j)
    {ze w : ModGL Tag.F4 Ω}
    (hw : ze⁻¹ * w ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)) :
    ∃ vΩ : StatedSp 3 Ω, ∀ U : Subgroup (StatedSp 3 Ω),
      ((U.map (MulAut.conj vΩ).toMonoidHom).map Φ).map
          (MulAut.conj ze).toMonoidHom =
        (U.map Φ).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨vΩ, hvΩ⟩ := exists_vOmega_implementing_untwist j hΦrange hw
  refine ⟨vΩ, fun U => map_conj_map_conj_eq_of_conj_eq_on_range Φ ?_⟩
  intro y hy
  rw [hΦrange] at hy
  exact hvΩ y hy

end ActualNeighbour

end CFSG.StandardType.F4ExplicitPos.NeighbourSquare

end

end
