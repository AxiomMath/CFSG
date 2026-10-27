module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.proposition_2_8

namespace CFSG
end CFSG
open CFSG

/-!
# The TI subset attached to the Brauer--Suzuki--Wall hypotheses
-/

namespace CFSG.GorensteinWalter

open BenderSuzuki.External

universe u

/-- Bender's conjugate-intersection hypothesis makes `K` a relative TI subset
with normalizer `H`.  This is the exact interface used by the
Brauer--Suzuki exceptional-character machinery. -/
public theorem BrauerSuzukiWallHypotheses.isTISubsetRelative
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    Suzuki.VI.IsTISubsetRelative h.H (h.K : Set G) := by
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hsNorm : h.s ∈ Subgroup.normalizer (h.K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [h.s_inverts_K x hx]
      exact h.K.inv_mem hx
    · intro hsx
      have hss : h.s * h.s = 1 := by
        simpa [pow_two] using h.s_involution.2
      have hsinv : h.s⁻¹ = h.s := by
        exact inv_eq_of_mul_eq_one_right hss
      have hinv := h.s_inverts_K (h.s * x * h.s⁻¹) hsx
      have hdouble : h.s * (h.s * x * h.s⁻¹) * h.s⁻¹ = x := by
        rw [hsinv]
        calc
          h.s * (h.s * x * h.s) * h.s =
              (h.s * h.s) * x * (h.s * h.s) := by group
          _ = x := by rw [hss]; simp
      have hxEq : x = (h.s * x * h.s⁻¹)⁻¹ := by
        exact hdouble.symm.trans hinv
      rw [hxEq]
      exact h.K.inv_mem hsx
  have hHNorm : h.H ≤ Subgroup.normalizer (h.K : Set G) := by
    rw [h.H_eq_join]
    exact sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.mpr hsNorm)
  have hKnontrivial : ∃ k : G, k ∈ (h.K : Set G) ∧ k ≠ 1 :=
    ⟨h.t, h.t_mem_K, h.t_involution.1⟩
  apply
    (Suzuki.VI.suzuki_ch6_proposition_2_8
      h.H (h.K : Set G) hKleH hHNorm hKnontrivial).2
  intro g hgH z hz
  have hzConj : z ∈ h.K.conjBy g := by
    rcases hz.1 with ⟨x, hxK, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨x, hxK, by simp [MulAut.conj_apply]⟩
  have hzOne : z = 1 :=
    Subgroup.disjoint_def.mp (h.conjugate_disjoint g hgH) hz.2 hzConj
  simpa using hzOne

end CFSG.GorensteinWalter
