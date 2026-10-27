module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactClosure
public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSecond
public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

namespace SpUFixGeom

variable {L : Type} [Group L] {R : Subgroup L} {F V : Type} [Field F] [AddCommGroup V]
  [Module F V]

theorem spUFixConclusion [Finite L] [Finite F] [CharP F 2] (G : SpUFixGeom L R F V)
    {Sy : Subgroup L} (hSy : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy) (hRSy : R ≤ Sy)
    (hSyR : Sy ≤ Subgroup.normalizer (R : Set L)) : SpUFixConclusion L R Sy := by
  intro α g hg hg2 hα2 hcomm hαSy hαR hfix
  by_contra hout
  have hSy2 : IsPGroup 2 Sy := by
    obtain ⟨P, hP⟩ := hSy
    exact hP ▸ P.isPGroup'
  obtain ⟨σ, ψ, hσ, hψ, hψi, hψβ, hψX⟩ := G.aut α hα2 hαR hout
  have haS : G.a ∈ G.rootSpan Sy :=
    Submodule.subset_span ⟨G.a_ne, G.a_iso, by rw [← G.R_eq]; exact hRSy⟩
  obtain ⟨u, hu0, huu, huX, hua⟩ := G.exists_le_sylow_not_smul hSy hSyR
  have huS : u ∈ G.rootSpan Sy := Submodule.subset_span ⟨hu0, huu, huX⟩
  have hψS : ∀ v ∈ G.rootSpan Sy, ψ v ∈ G.rootSpan Sy := fun v hv =>
    G.mem_rootSpan_of_aut α hαSy ψ hψ hψi hψβ hψX hv
  have hiso : ∀ s ∈ G.rootSpan Sy, G.β s s = 0 := fun s hs =>
    G.form_eq_zero_of_mem_rootSpan hSy2 hs hs
  have hψ2 : ∀ v ∈ G.rootSpan Sy, ∃ c : F, ψ (ψ v) = c • v := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact ⟨0, by simp⟩
    · have hψv_iso : G.β (ψ v) (ψ v) = 0 := hψβ v v (hiso v hv)
      have hmap1 : (G.X v).map α.toMonoidHom = G.X (ψ v) := hψX v (hiso v hv)
      have hmap2 : ((G.X v).map α.toMonoidHom).map α.toMonoidHom = G.X (ψ (ψ v)) := by
        rw [hmap1]
        exact hψX (ψ v) hψv_iso
      have hcomp : α.toMonoidHom.comp α.toMonoidHom = MonoidHom.id L := by
        ext x
        have hx : (α * α) x = x := by rw [hα2]; rfl
        simpa [MulAut.mul_apply] using hx
      have hαα : ((G.X v).map α.toMonoidHom).map α.toMonoidHom = G.X v := by
        rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      have hXeq : G.X (ψ (ψ v)) = G.X v := by rw [← hmap2, hαα]
      have hψψ_ne : ψ (ψ v) ≠ 0 := by
        intro h
        have h1 : ψ v = 0 := hψi (by simpa using h)
        exact hv0 (hψi (by simpa using h1))
      exact G.X_inj v (ψ (ψ v)) hv0 hψψ_ne (hiso v hv) (hψβ (ψ v) (ψ v) hψv_iso)
        hXeq.symm
  obtain ⟨M, hMi, hMβ, hMX, hM2⟩ := G.conj g⁻¹
  have hg2' : g⁻¹ * g⁻¹ = 1 := by
    have h : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
    rw [h, hg2]
  obtain ⟨c₀, hc₀⟩ := hM2 hg2'
  have hfix' : ∀ v ∈ G.rootSpan Sy, v ≠ 0 →
      ((∃ c : F, ψ v = c • v) ↔ (∃ c : F, M v = c • v)) := by
    intro v hv hv0
    have hroot : G.X v ∈ rootGroupsIn R Sy := by
      refine ⟨?_, G.le_of_mem_rootSpan hSy hv hv0⟩
      obtain ⟨x, hx⟩ := G.trans v hv0 (hiso v hv)
      refine ⟨x⁻¹, ?_⟩
      have hR : conjSubgroup (G.X G.a) x⁻¹ = conjSubgroup R x⁻¹ :=
        (congrArg (fun S => conjSubgroup S x⁻¹) G.R_eq).symm
      rw [← hR]
      simp only [conjSubgroup, inv_inv]
      exact hx
    have hiff := hfix (G.X v) hroot
    rw [hψX v (hiso v hv)] at hiff
    simp only [conjSubgroup] at hiff
    rw [hMX v (hiso v hv)] at hiff
    have hψ_ne : ψ v ≠ 0 := by
      intro h
      exact hv0 (hψi (by simpa using h))
    have hM_ne : M v ≠ 0 := by
      intro h
      exact hv0 (hMi (by simpa using h))
    have hψX_iff : G.X (ψ v) = G.X v ↔ ∃ c : F, ψ v = c • v := by
      constructor
      · intro h
        exact G.X_inj v (ψ v) hv0 hψ_ne (hiso v hv) (hψβ v v (hiso v hv)) h.symm
      · rintro ⟨c, hc⟩
        have hc0 : c ≠ 0 := by rintro rfl; exact hψ_ne (by simpa using hc)
        rw [hc, G.X_smul c v hc0 (hiso v hv)]
    have hMX_iff : G.X (M v) = G.X v ↔ ∃ c : F, M v = c • v := by
      constructor
      · intro h
        exact G.X_inj v (M v) hv0 hM_ne (hiso v hv)
          (by rw [hMβ v v]; exact hiso v hv) h.symm
      · rintro ⟨c, hc⟩
        have hc0 : c ≠ 0 := by rintro rfl; exact hM_ne (by simpa using hc)
        rw [hc, G.X_smul c v hc0 (hiso v hv)]
    rw [hψX_iff, hMX_iff] at hiff
    exact hiff
  exact spUFix_linear_false hσ ψ hψ hψi M hc₀ (G.rootSpan Sy) hψS hψ2 haS huS G.a_ne hua
    hfix'

end SpUFixGeom

end CFSG.LocalAnalysis.WeakClosure81

end
