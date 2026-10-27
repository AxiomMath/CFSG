module

public import CFSG.LocalAnalysis.StandardType.GGHalfLeviGlueAct
public import CFSG.LocalAnalysis.StandardType.GGHalfLeviGlueGraph
public import CFSG.LocalAnalysis.StandardType.GGHalfAux
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrameConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open CFSG.ComponentClassification.CatalogueBGraphForm

variable {G : Type} [Group G]

private theorem slGraphAut_slGraphAut {n : ℕ} (t : SpecialLinearGroup (Fin n) F2) :
    slGraphAut n F2 (slGraphAut n F2 t) = t := by
  have h := congrArg (fun f : MulAut (SpecialLinearGroup (Fin n) F2) => f t)
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.slGraph_mul_slGraph (n := n) (K := F2))
  simpa using h

theorem GGHalfTorusFrame.graph {Bs X : Subgroup G} {N : ℕ}
    {ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G}
    (h : GGHalfTorusFrame Bs X (halfTorusK N) ψ) :
    GGHalfTorusFrame Bs X (halfTorusK N) (ψ.comp (slGraphAut (N + 1) F2).toMonoidHom) where
  range := by
    rw [ggHalf_range_comp_of_surjective ψ (slGraphAut (N + 1) F2).surjective]
    exact h.range
  inj := h.inj.comp (slGraphAut (N + 1) F2).injective
  torus_le := by
    rintro _ ⟨t, ht, rfl⟩
    exact h.torus_le ⟨slGraphAut (N + 1) F2 t, slGraphAut_mem_halfTorusK ht, rfl⟩
  act := by
    intro b hb
    obtain ⟨t, ht, hact⟩ := h.act b hb
    refine ⟨slGraphAut (N + 1) F2 t, slGraphAut_mem_halfTorusK ht, fun l hl => ?_⟩
    have e : (ψ.comp (slGraphAut (N + 1) F2).toMonoidHom) (slGraphAut (N + 1) F2 t) = ψ t := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [slGraphAut_slGraphAut]
    rw [e]
    exact hact l hl

theorem ggHalfCoords_of_leviData {Bs L J K : Subgroup G} {x y : G} {m : ℕ} (hm : 2 ≤ m)
    {ψ₁ ψ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfLeviData Bs L J K x y m ψ₁ ψ₂) :
    ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G,
      GGHalfCoords Bs L J K m φ₁ φ₂ := by
  have hι₁ : Function.Injective (ψ₁.comp (slLower2Hom m)) :=
    h.frameL.inj.comp (slLower2Hom_injective m)
  have hι₂ : Function.Injective (ψ₂.comp (slUpper2Hom m)) :=
    h.frameK.inj.comp (slUpper2Hom_injective m)
  obtain ⟨θ, hθ⟩ := exists_mulAut_of_range_eq hι₂ hι₁ (h.levi₂.trans h.levi₁.symm)
  obtain ⟨c, ε, hε, hθc⟩ := aut_sl_gf2 (by omega : 3 ≤ m + 1) θ
  obtain ⟨ψ₂', hK', c', hc'⟩ : ∃ ψ₂' : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G,
      GGHalfTorusFrame Bs K (halfTorusK (m + 1 + 1)) ψ₂' ∧
      ∃ c : SpecialLinearGroup (Fin (m + 1)) F2,
        ∀ w, ψ₂' (slUpper2Hom m w) = ψ₁ (slLower2Hom m (c * w * c⁻¹)) := by
    interval_cases ε
    · refine ⟨ψ₂, h.frameK, c, fun w => ?_⟩
      have e : ψ₁ (slLower2Hom m (θ w)) = ψ₂ (slUpper2Hom m w) := hθ w
      rw [← e, hθc]
      simp [MulAut.mul_apply, MulAut.conj_apply]
    · refine ⟨ψ₂.comp (slGraphAut (m + 1 + 1 + 1) F2).toMonoidHom, h.frameK.graph, c, fun w => ?_⟩
      have e : ψ₁ (slLower2Hom m (θ (slGraphAut (m + 1) F2 w))) =
          ψ₂ (slUpper2Hom m (slGraphAut (m + 1) F2 w)) := hθ _
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [slGraphAut_slUpper2Hom, ← e, hθc]
      simp [MulAut.mul_apply, MulAut.conj_apply, slGraphAut_slGraphAut]
  have hnorm := levi_torus_conj_mem h.frameL hK' hc'
  set ĉ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := slUpper2Hom m c'⁻¹ with hĉ
  have hK'' : GGHalfTorusFrame Bs K (halfTorusK (m + 1 + 1))
      (ψ₂'.comp (MulAut.conj ĉ).toMonoidHom) := by
    refine hK'.conj ĉ ?_ ?_
    · intro t ht
      exact conj_slUpper2Hom_mem_halfTorusK (c := c'⁻¹)
        (fun s hs => by simpa using (hnorm s hs).2) ht
    · intro t ht
      have := conj_slUpper2Hom_mem_halfTorusK (c := c') (fun s hs => (hnorm s hs).1) ht
      simpa [hĉ, map_inv] using this
  refine ⟨ψ₁, ψ₂'.comp (MulAut.conj ĉ).toMonoidHom, ?_⟩
  exact
    { range₁ := h.frameL.range
      range₂ := hK''.range
      inj₁ := h.frameL.inj
      inj₂ := hK''.inj
      agree := by
        ext w
        have e : ĉ * slUpper2Hom m w * ĉ⁻¹ = slUpper2Hom m (c'⁻¹ * w * c') := by
          simp [hĉ, map_mul, map_inv]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [e, hc']
        congr 2
        group
      rangeJ := h.levi₁
      actL := h.frameL.act
      actK := hK''.act }

end CFSG.StandardType

end
