module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {M L : Subgroup (MulAut W)} {Z : Subgroup W}

private theorem s16c167_mem_stabSub_of_map_eq {Y : Subgroup W} {g : MulAut W}
    (hmap : Y.map g.toMonoidHom = Y) : g ∈ stabSub Y := by
  intro u
  constructor
  · intro hu
    have hu' : g u ∈ Y.map g.toMonoidHom := by rw [hmap]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := g.injective hwu
    exact this ▸ hw
  · intro hu
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩

theorem SevenCfg.eq_one_of_stab (h : SevenCfg M L Z) {x : MulAut W} (hxM : x ∈ M)
    (hx2 : x * x = 1) (hxY : ∀ Y ∈ conjSubs M Z, Y.map x.toMonoidHom = Y) : x = 1 := by
  refine h.eq_one_of_fix_all fun Y hY y hy => ?_
  have hxN : x ∈ normalizer (L : Set (MulAut W)) := h.le_normalizer hxM
  have hxst : x ∈ stabSub Y := s16c167_mem_stabSub_of_map_eq (hxY Y hY)
  obtain ⟨l₀, hl₀, y₀, hy₀, hly₀⟩ := h.exists_ne_of_mem hY
  have hl₀st : l₀ ∈ stabSub Y := s16c167_mem_stabSub_of_map_eq (h.map_eq_of_mem hl₀ hY)
  have hcard : Nat.card ↥Y = 8 := h.card_of_mem hY
  have hsq : ∀ u : ↥Y, u * u = 1 := fun u => Subtype.ext (h.sq (u : W))
  let r : MulAut ↥Y := resHom Y ⟨x, hxst⟩
  let l : MulAut ↥Y := resHom Y ⟨l₀, hl₀st⟩
  have hH : ∀ k ∈ autSub L Y, k ^ 7 = 1 := by
    intro k hk
    obtain ⟨g, hgL, rfl⟩ := mem_autSub.1 hk
    have hg7 : g ^ 7 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h.pow_seven hgL)
    rw [← map_pow, hg7, map_one]
  have hlH : l ∈ autSub L Y := mem_autSub.2 ⟨⟨l₀, hl₀st⟩, hl₀, rfl⟩
  have hl1 : l ≠ 1 := by
    intro hl
    have := congrArg (fun φ : MulAut ↥Y => ((φ ⟨y₀, hy₀⟩ : ↥Y) : W)) hl
    exact hly₀ this
  have hl7 : l ^ 7 = 1 := hH l hlH
  have hrlr : r * l * r⁻¹ ∈ autSub L Y := by
    refine mem_autSub.2 ⟨⟨x, hxst⟩ * ⟨l₀, hl₀st⟩ * ⟨x, hxst⟩⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hxN l₀).1 hl₀
    · rw [map_mul, map_mul, map_inv]
  have hr2 : r * r = 1 := by
    have : (⟨x, hxst⟩ : ↥(stabSub Y)) * ⟨x, hxst⟩ = 1 := Subtype.ext hx2
    show resHom Y ⟨x, hxst⟩ * resHom Y ⟨x, hxst⟩ = 1
    rw [← map_mul, this, map_one]
  have hr1 : r = 1 :=
    s16c167_seven_normalizer_trivial hcard hsq hl7 hl1 hr2
      (s16c167_seven_cyclic hcard hH hlH hl1 hrlr)
  have := congrArg (fun φ : MulAut ↥Y => ((φ ⟨y, hy⟩ : ↥Y) : W)) hr1
  exact this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
