module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnMain
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open CFSG.Assembly SmallOrth CFSG.RankThree.Classical2

section Transport

variable {M M' : Type} [Group M] [Group M']

theorem endData_mapEquiv (ψ : M ≃* M') {p : ℕ} {Ω A D : Subgroup M} {a : M} {Ω' : Subgroup M'}
    (hΩ : Ω.map ψ.toMonoidHom = Ω') (h : EndData p Ω A D a) :
    EndData p Ω' (A.map ψ.toMonoidHom) (D.map ψ.toMonoidHom) (ψ a) where
  A_le := hΩ ▸ Subgroup.map_mono h.A_le
  A_elem := TableB.isElemAbelian_map h.A_elem _
  D_le := hΩ ▸ Subgroup.map_mono h.D_le
  a_mem := ⟨a, h.a_mem, rfl⟩
  a_ne := fun h1 => h.a_ne (ψ.injective (by rw [h1, map_one]))
  D_cent := by
    rintro _ ⟨d, hd, rfl⟩
    show ψ d * ψ a = ψ a * ψ d
    rw [← map_mul, ← map_mul, h.D_cent d hd]
  D_norm := by
    intro c hc hca d' hd'
    obtain ⟨d, hd, rfl⟩ := hd'
    rw [← hΩ] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    have hc₀a : c₀ * a = a * c₀ := ψ.injective (by
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hca)
    refine ⟨c₀ * d * c₀⁻¹, h.D_norm c₀ hc₀ hc₀a d hd, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  D_qs := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (D.equivMapOfInjective ψ.toMonoidHom ψ.injective) h.D_qs
  A_cent := by
    rintro _ ⟨b, hb, rfl⟩ hbd
    have hb' : b ∈ Subgroup.zpowers a := h.A_cent b hb fun d hd => ψ.injective (by
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hbd _ ⟨d, hd, rfl⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨k, by simp only [MulEquiv.coe_toMonoidHom, ← map_zpow, hk]⟩

theorem bigConcl_of_mapEquiv (ψ : M ≃* M') {p : ℕ} {A D : Subgroup M}
    (h : BigConcl p (A.map ψ.toMonoidHom) (D.map ψ.toMonoidHom)) : BigConcl p A D := by
  obtain ⟨E, hE, hED, hEA, hcard⟩ := h
  refine ⟨E.map ψ.symm.toMonoidHom, TableB.isElemAbelian_map hE _, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨d, hd, hde⟩ := hED he
    have : ψ.symm e = d := by rw [← hde]; exact ψ.symm_apply_apply d
    show ψ.symm e ∈ D
    rw [this]
    exact hd
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨d, hd, hde⟩ := hEA he
    have : ψ.symm e = d := by rw [← hde]; exact ψ.symm_apply_apply d
    show ψ.symm e ∈ A
    rw [this]
    exact hd
  · rwa [Subgroup.card_map_of_injective ψ.symm.injective]

theorem normalizesTwoGroup_mapEquiv (ψ : M ≃* M') {Ω A : Subgroup M} {Ω' : Subgroup M'}
    (hΩ : Ω.map ψ.toMonoidHom = Ω') (h : NormalizesTwoGroup Ω A) :
    NormalizesTwoGroup Ω' (A.map ψ.toMonoidHom) := by
  obtain ⟨U, hUΩ, hU1, hU2, hAU⟩ := h
  refine ⟨U.map ψ.toMonoidHom, hΩ ▸ Subgroup.map_mono hUΩ, fun hbot => hU1 ?_, hU2.map _, ?_⟩
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ ψ.injective] at hbot
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hs' := Subgroup.mem_normalizer_iff.mp (hAU hs)
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨s * u * s⁻¹, (hs' u).mp hu, by simp only [map_mul, map_inv]⟩
    · rintro ⟨u', hu', hu'y⟩
      refine ⟨s⁻¹ * u' * s, (hs' _).mpr (by
        rw [show s * (s⁻¹ * u' * s) * s⁻¹ = u' by group]
        exact hu'), ?_⟩
      rw [map_mul, map_mul, map_inv, hu'y]
      group

end Transport

section Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem map_largeEvenOmega (Q' : QuadraticForm K (ι → K)) :
    (LargeEvenOmega (⇑Q')).map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
      orthDerived Q' := by
  rw [largeEvenOmega_def, Subgroup.map_commutator]
  have h : (LargeEvenOrthGroup (⇑Q')).map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q' := by
    rw [largeEvenOrthGroup_def, CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (Q := Q') rfl]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _
  rw [h]

end Matrix

end SmallOrthUn

end CFSG.StandardType

end
