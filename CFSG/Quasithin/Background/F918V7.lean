module

public import CFSG.Quasithin.Background.F918T5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

section Congr

variable {U U' : Type*} [CommGroup U] [CommGroup U']

theorem isFFStarOffender_map_congr_iff (e : U ≃* U') {G A : Subgroup (MulAut U)} :
    IsFFStarOffender (G.map (MulAut.congr e).toMonoidHom) (A.map (MulAut.congr e).toMonoidHom) ↔
      IsFFStarOffender G A :=
  isFFStarOffender_map_congr_equiv_iff e

theorem ffJ_map_mulAutCongr (e : U ≃* U') (G : Subgroup (MulAut U)) :
    ffJ (G.map (MulAut.congr e).toMonoidHom) = (ffJ G).map (MulAut.congr e).toMonoidHom := by
  have hsurj : Function.Surjective (MulAut.congr e).toMonoidHom := (MulAut.congr e).surjective
  apply le_antisymm
  · refine iSup₂_le fun B hB => ?_
    have hB' : IsFFStarOffender G (B.comap (MulAut.congr e).toMonoidHom) := by
      refine (isFFStarOffender_map_congr_iff e).mp ?_
      rw [Subgroup.map_comap_eq_self_of_surjective hsurj]
      exact hB
    have h1 : B.comap (MulAut.congr e).toMonoidHom ≤ ffJ G := le_iSup₂_of_le _ hB' le_rfl
    calc B = (B.comap (MulAut.congr e).toMonoidHom).map (MulAut.congr e).toMonoidHom :=
          (Subgroup.map_comap_eq_self_of_surjective hsurj B).symm
      _ ≤ (ffJ G).map (MulAut.congr e).toMonoidHom := Subgroup.map_mono h1
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le _ ((isFFStarOffender_map_congr_iff e).mpr hA) le_rfl

end Congr

section Conj

variable {X : Type} [CommGroup X]

theorem mem_stabSub_map_conj_iff (t x : MulAut X) (V₁ : Subgroup X) :
    x ∈ stabSub (V₁.map t.toMonoidHom) ↔ t⁻¹ * x * t ∈ stabSub V₁ := by
  simp only [mem_stabSub, Subgroup.mem_map_equiv, MulAut.mul_apply]
  constructor
  · intro h u
    have := h (t u)
    simpa [MulAut.inv_apply] using this
  · intro h w
    have := h (t.symm w)
    simpa [MulAut.inv_apply] using this

theorem autSub_conj_map_eq (t : MulAut X) (H : Subgroup (MulAut X)) (V₁ : Subgroup X) :
    autSub (H.map (MulAut.conj t).toMonoidHom) (V₁.map t.toMonoidHom) =
      (autSub H V₁).map (MulAut.congr (restrictAutEquiv t V₁)).toMonoidHom := by
  ext φ
  rw [mem_autSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g, ⟨h, hh, hhg⟩, rfl⟩
    have e1 : t⁻¹ * (g : MulAut X) * t = h := by
      rw [← hhg]
      simp [MulAut.conj_apply, mul_assoc]
    have hstab : h ∈ stabSub V₁ := by
      have := (mem_stabSub_map_conj_iff t g V₁).mp g.2
      rwa [e1] at this
    refine ⟨resHom V₁ ⟨h, hstab⟩, mem_autSub.mpr ⟨⟨h, hstab⟩, hh, rfl⟩, ?_⟩
    ext w
    have e2 : (g : MulAut X) = t * h * t⁻¹ := by
      rw [← hhg]
      simp [MulAut.conj_apply]
    show t (h (t.symm (w : X))) = (g : MulAut X) (w : X)
    rw [e2]
    simp [MulAut.mul_apply, MulAut.inv_apply]
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.mp hψ
    have hgm : t * (g : MulAut X) * t⁻¹ ∈ stabSub (V₁.map t.toMonoidHom) := by
      rw [mem_stabSub_map_conj_iff]
      simp [mul_assoc]
    refine ⟨⟨t * g * t⁻¹, hgm⟩, ⟨g, hgH, by simp [MulAut.conj_apply]⟩, ?_⟩
    ext w
    show (t * (g : MulAut X) * t⁻¹) (w : X) = t ((g : MulAut X) (t.symm (w : X)))
    simp [MulAut.mul_apply, MulAut.inv_apply]

theorem conj_map_eq_self {Tb Lb : Subgroup (MulAut X)} {t : MulAut X}
    (hTL : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb) (ht : t ∈ Tb) :
    Lb.map (MulAut.conj t).toMonoidHom = Lb := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    exact hTL t ht l hl
  · intro x hx
    refine ⟨t⁻¹ * x * t, ?_, ?_⟩
    · simpa using hTL t⁻¹ (Tb.inv_mem ht) x hx
    · simp [MulAut.conj_apply, mul_assoc]

theorem conj_sup_inf_eq {Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hTL : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb) (ht : t ∈ Tb) :
    (Lb ⊔ (Tb ⊓ stabSub V₁)).map (MulAut.conj t).toMonoidHom =
      Lb ⊔ (Tb ⊓ stabSub (V₁.map t.toMonoidHom)) := by
  have hL : Lb.map (MulAut.conj t).toMonoidHom = Lb := conj_map_eq_self hTL ht
  have hT : Tb.map (MulAut.conj t).toMonoidHom = Tb := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact Tb.mul_mem (Tb.mul_mem ht hs) (Tb.inv_mem ht)
    · intro x hx
      refine ⟨t⁻¹ * x * t, Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) hx) ht, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hS : (stabSub V₁).map (MulAut.conj t).toMonoidHom = stabSub (V₁.map t.toMonoidHom) := by
    ext x
    rw [mem_stabSub_map_conj_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      refine ⟨t⁻¹ * x * t, hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hL, hT, hS]

theorem ffJ_map_conj {Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hTL : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb) (ht : t ∈ Tb)
    (hffJ : ffJ (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) = autSub Lb V₁) :
    ffJ (autSub (Lb ⊔ (Tb ⊓ stabSub (V₁.map t.toMonoidHom))) (V₁.map t.toMonoidHom)) =
      autSub Lb (V₁.map t.toMonoidHom) := by
  rw [← conj_sup_inf_eq hTL ht, autSub_conj_map_eq, ffJ_map_mulAutCongr, hffJ, ← autSub_conj_map_eq,
    conj_map_eq_self hTL ht]

end Conj

end CFSG.Quasithin
