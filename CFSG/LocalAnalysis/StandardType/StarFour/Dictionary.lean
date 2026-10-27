module

public import CFSG.LocalAnalysis.StandardType.StarFour.FrameNesting
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSLBlock

public section

namespace CFSG.StandardType.StarFour

theorem inf_centralizer_eq_map_centralizer {G X : Type} [Group G] [Group X] (ψ : G →* X)
    (hψ : Function.Injective ψ) (S : Set X) (hat : X → G)
    (hS : ∀ b ∈ S, ∀ u : G, b * ψ u * b⁻¹ = ψ (hat b * u * (hat b)⁻¹)) :
    ψ.range ⊓ Subgroup.centralizer S = (Subgroup.centralizer (hat '' S)).map ψ := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxrange, hxcent⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hxrange
    refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hxcent
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    obtain ⟨b, hb, rfl⟩ := hh'
    have hconj : b * ψ u * b⁻¹ = ψ u := mul_inv_eq_iff_eq_mul.mpr (hxcent b hb)
    have hhat : hat b * u * (hat b)⁻¹ = u := by
      apply hψ
      rw [← hS b hb u, hconj]
    exact mul_inv_eq_iff_eq_mul.mp hhat
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_inf]
    refine ⟨MonoidHom.mem_range.mpr ⟨u, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbu : hat b * u = u * hat b := hu (hat b) (Set.mem_image_of_mem hat hb)
    have hhat : hat b * u * (hat b)⁻¹ = u := mul_inv_eq_iff_eq_mul.mpr hbu
    have hconj : b * ψ u * b⁻¹ = ψ u := by
      rw [hS b hb u, hhat]
    exact mul_inv_eq_iff_eq_mul.mp hconj

theorem repCentSL_groupRep {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    {P : Type} [CommGroup P] (η : P →* SpecialLinearGroup F V) :
    repCentSL (groupRep η) = Subgroup.centralizer (η.range : Set (SpecialLinearGroup F V)) := by
  ext g
  rw [repCentSL, Subgroup.mem_comap, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp ha
    have hw := h (groupRep η p) (Set.mem_range_self p)
    have hw' : SpecialLinearGroup.toLinearEquiv a * SpecialLinearGroup.toLinearEquiv g
        = SpecialLinearGroup.toLinearEquiv g * SpecialLinearGroup.toLinearEquiv a := by
      rw [← hp]
      exact hw
    exact SpecialLinearGroup.toLinearEquiv_injective (by
      rw [map_mul, map_mul]
      exact hw')
  · intro h a ha
    obtain ⟨p, hp⟩ := Set.mem_range.mp ha
    have hpcomm : η p * g = g * η p := h (η p) (MonoidHom.mem_range.mpr ⟨p, rfl⟩)
    have hw : SpecialLinearGroup.toLinearEquiv (η p) * SpecialLinearGroup.toLinearEquiv g
        = SpecialLinearGroup.toLinearEquiv g * SpecialLinearGroup.toLinearEquiv (η p) := by
      rw [← map_mul, ← map_mul, hpcomm]
    rw [← hp]
    exact hw

end CFSG.StandardType.StarFour
