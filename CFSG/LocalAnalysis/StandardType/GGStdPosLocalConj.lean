module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPosLocalHyp_comp_conj
    {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGKGPosLocalHyp p Bs X t n f ψ) (k : (ggU t n f).K) :
    GGKGPosLocalHyp p Bs X t n f (ψ.comp (MulAut.conj k).toMonoidHom) := by
  obtain ⟨hA, ⟨hker, hrange, ht, hp⟩, hC, hdiag, hE⟩ := h
  have hr : (ψ.comp (MulAut.conj k).toMonoidHom).range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj k).surjective,
      Subgroup.map_top, hrange]
  refine ⟨hA, ⟨fun z hz => ?_, hr, ht, hp⟩, hC, fun b hb => ?_, hE⟩
  · have hc := hker (show ψ (k * z * k⁻¹) = 1 from hz)
    have := Subgroup.Normal.conj_mem inferInstance _ hc k⁻¹
    simpa [mul_assoc] using this
  · obtain ⟨g, hg, hγ⟩ := hdiag b hb
    have ha : ψ k ∈ X := hrange ▸ ⟨k, rfl⟩
    have hbaX : b⁻¹ * ψ k * b ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hC.2.1 (inv_mem hb)) (ψ k)).mp ha
      simpa using this
    refine ⟨b⁻¹ * ψ k * b * g * (ψ k)⁻¹, hr ▸ ?_, fun γ hγ' => ?_⟩
    · exact mul_mem (mul_mem hbaX (hrange ▸ hg)) (inv_mem ha)
    · obtain ⟨h, hh, hz⟩ := hγ γ hγ'
      refine ⟨h, hh, fun z hz' => ?_⟩
      have e := hz z hz'
      have e2 : ∀ w, (ψ.comp (MulAut.conj k).toMonoidHom) w = ψ k * ψ w * (ψ k)⁻¹ := fun w => by
        simp [MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv]
      rw [e2, e2]
      calc _ = ψ k * ((b * g)⁻¹ * ψ z * (b * g)) * (ψ k)⁻¹ := by group
        _ = _ := by rw [e]

end CFSG.StandardType

end
