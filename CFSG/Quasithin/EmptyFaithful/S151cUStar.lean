module

public import CFSG.Quasithin.EmptyFaithful.S151cSetting

public section

namespace CFSG.Quasithin

open CFSG.Open

section UStar151c

structure UStar {W : Type*} [CommGroup W] [Finite W] (Xr H Ξ : Subgroup (MulAut W)) : Prop where
  isP : IsPGroup 2 H
  hU : ∀ z : W, z ∈ fixV H → z ≠ 1 → ∀ ψ ∈ Xr, ψ z = z → ψ ∈ Ξ
  star : ∀ B : Subgroup W, B ≠ ⊥ → (∀ ψ ∈ Xr, ∀ w ∈ B, ψ w ∈ B) →
    ¬ B ≤ Subgroup.closure {x | ∃ ψ ∈ Ξ, ∃ z ∈ fixV H ⊓ B, ψ z = x}

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

omit [Finite V] in
theorem le_stabSub_of_invariant {U : Subgroup V} (hU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) :
    X ≤ stabSub U := by
  intro x hx u
  refine ⟨fun h => ?_, fun h => hU x hx u h⟩
  have := hU x⁻¹ (X.inv_mem hx) _ h
  simpa using this

theorem Setting151c.uStar (h : Setting151c X Tb Xc) {U : Subgroup V}
    (hU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) :
    UStar (autSub X U) (autSub Tb U) (autSub Xc U) := by
  have hXs : X ≤ stabSub U := le_stabSub_of_invariant hU
  have hTs : Tb ≤ stabSub U := h.syl.1.trans hXs
  refine ⟨isPGroup_autSub h.syl.2.1, ?_, ?_⟩
  · intro z hz hz1 ψ hψ hψz
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hψ
    have hzT : (z : V) ∈ fixV Tb := fun t ht => (mem_fixV_autSub.mp hz) t ht (hTs ht)
    have hz1' : (z : V) ≠ 1 := fun e => hz1 (Subtype.ext e)
    have hZ1 : Subgroup.zpowers (z : V) ≤ fixV Tb := Subgroup.zpowers_le.mpr hzT
    have hZ1ne : Subgroup.zpowers (z : V) ≠ ⊥ := fun e => hz1' (Subgroup.zpowers_eq_bot.mp e)
    have hgz : (g : MulAut V) (z : V) = z := congrArg (fun w : U => (w : V)) hψz
    have hgX : (g : MulAut V) ∈ X ⊓ centSub (Subgroup.zpowers (z : V)) := by
      refine ⟨hg, ?_⟩
      intro u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [map_zpow, hgz]
    exact mem_autSub.mpr ⟨g, h.hU _ hZ1 hZ1ne hgX, rfl⟩
  · intro B hB hBinv hle
    have hBX : ∀ x ∈ X, ∀ w ∈ B.map U.subtype, x w ∈ B.map U.subtype := by
      rintro x hx _ ⟨b, hb, rfl⟩
      have hxs : x ∈ stabSub U := hXs hx
      have hmem : resHom U ⟨x, hxs⟩ ∈ autSub X U := mem_autSub.mpr ⟨⟨x, hxs⟩, hx, rfl⟩
      exact ⟨resHom U ⟨x, hxs⟩ b, hBinv _ hmem b hb, rfl⟩
    have hne : B.map U.subtype ≠ ⊥ := by
      intro e
      apply hB
      rw [Subgroup.map_eq_bot_iff_of_injective B U.subtype_injective] at e
      exact e
    refine h.star (B.map U.subtype) hne hBX ?_
    have h1 : B.map U.subtype ≤ (Subgroup.closure {x | ∃ ψ ∈ autSub Xc U,
        ∃ z ∈ fixV (autSub Tb U) ⊓ B, ψ z = x}).map U.subtype := Subgroup.map_mono hle
    refine h1.trans ?_
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨ψ, hψ, z, hz, rfl⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hψ
    refine ⟨g, hg, (z : V), ⟨?_, z, hz.2, rfl⟩, rfl⟩
    exact fun t ht => (mem_fixV_autSub.mp hz.1) t ht (hTs ht)

end UStar151c

end CFSG.Quasithin
