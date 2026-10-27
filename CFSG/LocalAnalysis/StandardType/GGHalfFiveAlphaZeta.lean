module

public import CFSG.LocalAnalysis.StandardType.GGHalfAlphaPre
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes
public import CFSG.LocalAnalysis.StandardType.GGHalfAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

private theorem conj_mul_inv_cancel {G : Type*} [Group G] {a b t : G}
    (hab : a * b * a⁻¹ = a * t * a⁻¹) : b = t := by
  have h' : a * b = a * t := by
    have := congrArg (fun z => z * a) hab
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
  exact mul_left_cancel h'

include h

theorem alpha_zeta5 {α : MulAut (SpecialLinearGroup (Fin 6) F2)}
    (hα : ∀ s, hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹ = gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹) :
    α zeta5 = zeta5 := by
  have key : ∀ {s t : SpecialLinearGroup (Fin 6) F2},
      gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹ = hElt φ₂ * φ₁ t * (hElt φ₂)⁻¹ → α s = t := by
    intro s t hst
    have h1 : hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹ =
        hElt φ₂ * φ₁ t * (hElt φ₂)⁻¹ := by rw [hα s, hst]
    exact h.coords.inj₁ (conj_mul_inv_cancel h1)
  have h0 : α (omegaBlock 5 0) = omegaBlock 5 0 := key (alpha_v h)
  have h2 : α (omegaBlock 5 2) = omegaBlock 5 4 := by
    refine key ?_
    have hmem : omegaBlock 3 (⟨2, by omega⟩ : Fin 3) ∈ slOn 4 {j : Fin 4 | 2 ≤ j.val} := by
      apply omegaBlock_mem_slOn
      · show 2 ≤ (((⟨2, by omega⟩ : Fin 3).castSucc : Fin 4)).val
        simp only [Fin.val_castSucc, Fin.val_mk]
        omega
      · show 2 ≤ (((⟨2, by omega⟩ : Fin 3).succ : Fin 4)).val
        simp only [Fin.val_succ, Fin.val_mk]
        omega
    have hl := alpha_lower h (omegaBlock 3 (⟨2, by omega⟩ : Fin 3)) hmem
    rw [slUpper2Hom_omegaBlock, slLower2Hom_omegaBlock] at hl
    exact hl
  have h4 : α (omegaBlock 5 4) = omegaBlock 5 2 := key (alpha_w h)
  have hcomm : omegaBlock 5 4 * omegaBlock 5 2 = omegaBlock 5 2 * omegaBlock 5 4 :=
    (omegaBlock_comm (n := 5) (k := (⟨2, by omega⟩ : Fin 5)) (k' := (⟨4, by omega⟩ : Fin 5))
      (by norm_num)).symm
  calc α zeta5 = α (omegaBlock 5 0 * omegaBlock 5 2 * omegaBlock 5 4) := by rw [zeta5]
    _ = α (omegaBlock 5 0) * α (omegaBlock 5 2) * α (omegaBlock 5 4) := by rw [map_mul, map_mul]
    _ = omegaBlock 5 0 * omegaBlock 5 4 * omegaBlock 5 2 := by rw [h0, h2, h4]
    _ = omegaBlock 5 0 * omegaBlock 5 2 * omegaBlock 5 4 := by rw [mul_assoc, hcomm, ← mul_assoc]

end GGHalfCtx

end CFSG.StandardType

end
