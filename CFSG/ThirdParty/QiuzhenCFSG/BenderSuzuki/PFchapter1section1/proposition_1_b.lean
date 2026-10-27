module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 1(b)
-/

public theorem proposition_1_b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ X : Subgroup G, X ≠ ⊥ → X ≤ Q →
      Subgroup.normalizer (X : Set G) ≤ H := by
  classical
  intro X hXne hXQ g hgNorm
  by_contra hgH
  obtain ⟨h, hHD, _hodd⟩ := proposition_1_a H D Q t hA1 g hgH
  have hX_le_inter : X ≤ rightConjugate H g ⊓ H := by
    intro x hx
    constructor
    · have hxHconj : g * x * g⁻¹ ∈ H := hA1.Q_le_H (hXQ ((Subgroup.mem_normalizer_iff.mp hgNorm x).1 hx))
      exact ⟨g * x * g⁻¹, hxHconj, by
        calc
          (MulAut.conj g⁻¹) (g * x * g⁻¹) =
              g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := rfl
          _ = x := by group⟩
    · exact hA1.Q_le_H (hXQ hx)
  have hQDconj_bot : Q ⊓ rightConjugate D (h : G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx.2 with ⟨d, hdD, rfl⟩
    have hhH : (h : G) ∈ H := h.property
    have hconjQ : (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ ∈ Q := by
      have hxQH :
          (((h : G)⁻¹ * d * (h : G)) : G) ∈ Q := by
        simpa [MulAut.conj_apply] using hx.1
      have hxQsub :
          (⟨((h : G)⁻¹ * d * (h : G)), hA1.Q_le_H hxQH⟩ : H) ∈ Q.subgroupOf H := hxQH
      have hnormal := hA1.Q_normal_in_H
      have hmem :=
        hnormal.conj_mem
          (⟨((h : G)⁻¹ * d * (h : G)), hA1.Q_le_H hxQH⟩ : H)
          hxQsub h
      exact hmem
    have hconjD : (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ ∈ D := by
      simpa [mul_assoc] using hdD
    have hmemInf : (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ ∈ Q ⊓ D :=
      ⟨hconjQ, hconjD⟩
    have hbot : (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ = 1 := by
      have := hA1.Q_disjoint_D.le_bot hmemInf
      simpa using this
    have hd_one : d = 1 := by
      calc
        d = (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ := by group
        _ = 1 := hbot
    calc
      (MulAut.conj (h : G)⁻¹) d =
          (h : G)⁻¹ * d * ((h : G)⁻¹)⁻¹ := rfl
      _ = 1 := by simp [hd_one]
  have hX_le_bot : X ≤ ⊥ := by
    intro x hx
    rw [← hQDconj_bot]
    exact ⟨hXQ hx, by simpa [← hHD] using hX_le_inter hx⟩
  apply hXne
  exact le_bot_iff.mp hX_le_bot

end PFchapter1section1
end CFSG.BenderSuzuki
