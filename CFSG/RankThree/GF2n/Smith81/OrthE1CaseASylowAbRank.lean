module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

section Linear

variable {K : Type} [Field K]

theorem range_beta_eq_of_section (S : QSpace K) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) (σ : V →ₗ[K] S.E) (hσ : ∀ v : V, β (σ v) = v) :
    LinearMap.range β = V := by
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    exact hβ.range e
  · intro v hv
    exact LinearMap.mem_range.mpr ⟨σ ⟨v, hv⟩, hσ ⟨v, hv⟩⟩

theorem sub_one_mem_of_beta (S : QSpace K) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) (T : S.E →ₗ[K] S.E) (hTβ : ∀ e, T (β e) = β (T e))
    {v : S.E} (hv : v ∈ V) : (T - 1) v ∈ V := by
  apply hβ.ker
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← hTβ v, hβ.kills v hv, map_zero,
    sub_zero]

theorem map_sub_one_le_inf (S : QSpace K) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) (T : S.E →ₗ[K] S.E) (hTβ : ∀ e, T (β e) = β (T e)) :
    V.map (T - 1) ≤ LinearMap.range (T - 1) ⊓ V := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
  exact ⟨LinearMap.mem_range_self _ _, sub_one_mem_of_beta S hβ T hTβ hv⟩

theorem finrank_range_sub_one_split (S : QSpace K) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) (σ : V →ₗ[K] S.E) (hσ : ∀ v : V, β (σ v) = v)
    (T : S.E →ₗ[K] S.E) (hTβ : ∀ e, T (β e) = β (T e)) :
    Module.finrank K (LinearMap.range (T - 1)) =
      Module.finrank K (V.map (T - 1)) +
        Module.finrank K ↥(LinearMap.range (T - 1) ⊓ V) := by
  have hrβ : LinearMap.range β = V := range_beta_eq_of_section S hβ σ hσ
  have hcomm : β.comp (T - 1) = (T - 1).comp β := by
    ext e
    simp [hTβ e]
  have himg : (LinearMap.range (T - 1)).map β = V.map (T - 1) := by
    rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp, hrβ]
  have hrange : LinearMap.range (β.domRestrict (LinearMap.range (T - 1))) =
      V.map (T - 1) := by
    rw [← himg, show β.domRestrict (LinearMap.range (T - 1)) =
      β.comp (LinearMap.range (T - 1)).subtype from rfl, LinearMap.range_comp,
      Submodule.range_subtype]
  have hker : LinearMap.ker (β.domRestrict (LinearMap.range (T - 1))) =
      Submodule.comap (LinearMap.range (T - 1)).subtype (LinearMap.range (T - 1) ⊓ V) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf]
    constructor
    · intro h
      have h' : β x = 0 := h
      exact ⟨x.2, hβ.ker _ h'⟩
    · intro h
      exact hβ.kills _ h.2
  have hfin := LinearMap.finrank_range_add_finrank_ker
    (β.domRestrict (LinearMap.range (T - 1)))
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : LinearMap.range (T - 1) ⊓ V ≤ LinearMap.range (T - 1))).finrank_eq] at hfin
  exact hfin.symm

theorem two_mul_rank_le (S : QSpace K) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) (σ : V →ₗ[K] S.E) (hσ : ∀ v : V, β (σ v) = v)
    (T : S.E →ₗ[K] S.E) (hTβ : ∀ e, T (β e) = β (T e)) :
    2 * Module.finrank K (V.map (T - 1)) ≤ Module.finrank K (LinearMap.range (T - 1)) := by
  have h := Submodule.finrank_mono (map_sub_one_le_inf S hβ T hTβ)
  rw [finrank_range_sub_one_split S hβ σ hσ T hTβ]
  omega

theorem finrank_map_sub_eq_rank {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : QSpace K) {V : Submodule K S.E} (cV : V ≃ₗ[K] (ι → K)) (T : S.E →ₗ[K] S.E)
    (A : Matrix ι ι K) (hA : ∀ (v : S.E) (hv : v ∈ V), ∃ hTv : T v ∈ V,
      cV ⟨T v, hTv⟩ = A *ᵥ cV ⟨v, hv⟩) :
    Module.finrank K (V.map (T - 1)) = (A - 1).rank := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (ι → K) →ₗ[K] S.E, ∀ x, ψ x = ((cV.symm x : V) : S.E) :=
    ⟨V.subtype.comp cV.symm.toLinearMap, fun x => rfl⟩
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    rw [hψ, hψ] at hxy
    exact cV.symm.injective (Subtype.ext hxy)
  have hψrange : LinearMap.range ψ = V := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hψ]
      exact (cV.symm x).2
    · intro v hv
      refine LinearMap.mem_range.mpr ⟨cV ⟨v, hv⟩, ?_⟩
      simp [hψ]
  have hkey : ∀ x : ι → K, (T - 1) (ψ x) = ψ ((A - 1) *ᵥ x) := by
    intro x
    obtain ⟨v, rfl⟩ : ∃ v : V, cV v = x := ⟨cV.symm x, LinearEquiv.apply_symm_apply cV x⟩
    obtain ⟨hTv, h⟩ := hA (v : S.E) v.2
    have h' : cV ⟨T (v : S.E), hTv⟩ = A *ᵥ cV v := h
    have hmem : T (v : S.E) - (v : S.E) ∈ V := V.sub_mem hTv v.2
    have hsub : (⟨T (v : S.E) - (v : S.E), hmem⟩ : V) = ⟨T (v : S.E), hTv⟩ - v := by
      ext
      simp
    have h2 : cV ⟨T (v : S.E) - (v : S.E), hmem⟩ = (A - 1) *ᵥ cV v := by
      rw [hsub, map_sub, h', Matrix.sub_mulVec, Matrix.one_mulVec]
    have h3 : cV.symm ((A - 1) *ᵥ cV v) = ⟨T (v : S.E) - (v : S.E), hmem⟩ := by
      rw [← h2, LinearEquiv.symm_apply_apply]
    simp only [hψ, LinearEquiv.symm_apply_apply, h3, LinearMap.sub_apply, Module.End.one_apply]
  have hcomp : (T - 1).comp ψ = ψ.comp (A - 1).mulVecLin :=
    LinearMap.ext fun x => hkey x
  calc Module.finrank K (V.map (T - 1))
      = Module.finrank K (LinearMap.range ((T - 1).comp ψ)) := by
        rw [LinearMap.range_comp, hψrange]
    _ = Module.finrank K (LinearMap.range (ψ.comp (A - 1).mulVecLin)) := by
        rw [hcomp]
    _ = Module.finrank K (LinearMap.range (A - 1).mulVecLin) := by
        rw [LinearMap.range_comp]
        exact (Submodule.equivMapOfInjective ψ hψinj
          (LinearMap.range (A - 1).mulVecLin)).finrank_eq.symm
    _ = (A - 1).rank := rfl

theorem rank_le_four (S : QSpace K) (h8 : Module.finrank K S.E = 8) (T : S.E →ₗ[K] S.E)
    (hT : (T - 1) * (T - 1) = 0) : Module.finrank K (LinearMap.range (T - 1)) ≤ 4 := by
  have hle : LinearMap.range (T - 1) ≤ LinearMap.ker (T - 1) := by
    rintro _ ⟨e, rfl⟩
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun hT e
    rw [Module.End.mul_apply, LinearMap.zero_apply] at h
    exact h
  have h1 := LinearMap.finrank_range_add_finrank_ker (T - 1)
  have h2 := Submodule.finrank_mono hle
  rw [h8] at h1
  omega

end Linear

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
