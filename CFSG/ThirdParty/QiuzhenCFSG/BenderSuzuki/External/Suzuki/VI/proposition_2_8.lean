module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.definition_2_7
import Mathlib.Tactic.Group

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki VI.(2.8)

The conjugate-intersection criterion for a trivial-intersection subset.
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u

/-- Suzuki, *Group Theory II*, Chapter 6, (2.8). -/
public theorem suzuki_ch6_proposition_2_8
    {G : Type u} [Group G] (H : Subgroup G) (K : Set G)
    (hKH : K ⊆ H) (hHnorm : H ≤ Subgroup.normalizer K)
    (hKnontrivial : ∃ k : G, k ∈ K ∧ k ≠ 1) :
    IsTISubsetRelative H K ↔
      ∀ g : G, g ∉ H →
        (((fun x : G => g * x * g⁻¹) '' K) ∩ K) ⊆ ({1} : Set G) := by
  constructor
  · rintro ⟨_, _, hfusion, hcentralizer⟩ g hgH z ⟨⟨x, hxK, rfl⟩, hzxK⟩
    simp only [Set.mem_singleton_iff]
    by_contra hz_ne
    have hx_ne : x ≠ 1 := by
      intro hx
      subst x
      simp at hz_ne
    obtain ⟨h, hh⟩ := hfusion hxK hzxK ⟨g, rfl⟩
    have hh' : g * x * g⁻¹ = (h : G) * x * (h : G)⁻¹ := by
      simpa using hh.symm
    have hc : (h : G)⁻¹ * g ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha_eq : a = x := by simpa using ha
      subst a
      calc
        x * ((h : G)⁻¹ * g) =
            (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * g := by group
        _ = (h : G)⁻¹ * (g * x * g⁻¹) * g := by rw [hh']
        _ = ((h : G)⁻¹ * g) * x := by group
    have hcH : (h : G)⁻¹ * g ∈ H := hcentralizer x hxK hx_ne hc
    have hgH' : g ∈ H := by
      have := H.mul_mem h.property hcH
      simpa using this
    exact hgH hgH'
  · intro hintersection
    refine ⟨hKH, ?_, ?_, ?_⟩
    · apply le_antisymm
      · intro g hgNorm
        by_contra hgH
        obtain ⟨k, hkK, hk_ne⟩ := hKnontrivial
        have hgNorm' : ∀ x : G, x ∈ K ↔ g * x * g⁻¹ ∈ K := by
          exact Subgroup.mem_set_normalizer_iff.mp hgNorm
        have hmem : g * k * g⁻¹ ∈
            ((fun x : G => g * x * g⁻¹) '' K) ∩ K :=
          ⟨⟨k, hkK, rfl⟩, (hgNorm' k).1 hkK⟩
        have hone := hintersection g hgH hmem
        have : g * k * g⁻¹ = 1 := by simpa using hone
        apply hk_ne
        have := congrArg (fun z : G => g⁻¹ * z * g) this
        simpa [mul_assoc] using this
      · exact hHnorm
    · intro x y hxK hyK hxy
      obtain ⟨g, rfl⟩ := hxy
      by_cases hgH : g ∈ H
      · exact ⟨⟨g, hgH⟩, rfl⟩
      · by_cases hx : x = 1
        · subst x
          exact ⟨1, by simp⟩
        · have hmem : g * x * g⁻¹ ∈
              ((fun z : G => g * z * g⁻¹) '' K) ∩ K :=
            ⟨⟨x, hxK, rfl⟩, hyK⟩
          have hone := hintersection g hgH hmem
          have hconj_one : g * x * g⁻¹ = 1 := by simpa using hone
          exfalso
          apply hx
          have := congrArg (fun z : G => g⁻¹ * z * g) hconj_one
          simpa [mul_assoc] using this
    · intro x hxK hx_ne g hgCentralizer
      by_contra hgH
      have hcomm : g * x = x * g :=
        ((Subgroup.mem_centralizer_iff.mp hgCentralizer) x (by simp)).symm
      have hconj : g * x * g⁻¹ = x := by
        calc
          g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
          _ = x := by simp
      have hmem : g * x * g⁻¹ ∈
          ((fun z : G => g * z * g⁻¹) '' K) ∩ K :=
        ⟨⟨x, hxK, rfl⟩, by simpa [hconj] using hxK⟩
      have hone := hintersection g hgH hmem
      apply hx_ne
      simpa [hconj] using hone

end VI
end Suzuki
end External
end CFSG.BenderSuzuki
