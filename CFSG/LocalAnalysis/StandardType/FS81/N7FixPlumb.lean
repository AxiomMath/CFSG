module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixDefs
public import CFSG.LocalAnalysis.StandardType.FS81.AutMat
import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

theorem N7Setup.exists_of_cases (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
    (B : Basis3 G (Row.twD7.n + 1)) (hB : Adapted B b₀ K E) (hfus : Fus42 B b₀)
    (hodd : OddCoreTrivial E)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) =
      evenFix0 Row.twD7.n) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X), Nonempty (N7Setup X) := by
  classical
  obtain ⟨hspan, hb0, -⟩ := hB
  subst hspan
  set X := ggAutomizer ⊤ B.span with hX
  have : Finite (MulAut ↥B.span) :=
    Finite.of_injective (fun f : MulAut ↥B.span => (f : ↥B.span → ↥B.span)) DFunLike.coe_injective
  have : Fintype ↥X := Fintype.ofFinite _
  have hcond : ∀ (φ : MulAut ↥B.span) (x : G),
      (∀ b : ↥B.span, ((φ b : ↥B.span) : G) = x * b * x⁻¹) →
      (∃ c : ZMod 3, B.matOf φ *ᵥ e0 = c • e0) →
      x ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    intro φ x hφ h
    obtain ⟨c, hc⟩ := h
    have hconj := B.conj_b_of_mulVec_single hφ (i := 0) hc
    rw [hb0] at hconj
    exact Basis3.mem_normalizer_zpowers_of_conj (by rw [hconj]; exact Subgroup.npow_mem_zpowers _ _)
  refine ⟨↥X, inferInstance, inferInstance, ⟨?_⟩⟩
  refine ⟨B.matHom.comp X.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext (B.matOf_injective h)
  · intro M hM
    have hM' : M ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
      rw [hN0]; exact hM
    obtain ⟨φ, hφ, hφM⟩ :=
      (B.mem_realized_iff (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) M).mp hM'
    obtain ⟨g, hgN0, hgN, hg⟩ := hφ
    exact ⟨⟨φ, mem_ggAutomizer_iff.mpr ⟨g, trivial, hgN, hg⟩⟩, hφM⟩
  · intro x
    constructor
    · intro hx
      exact ⟨1, by rw [evenFix0_mulVec_e0 hx, one_smul]⟩
    · rintro ⟨c, hc⟩
      obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp x.2
      have hgN0 := hcond (x : MulAut ↥B.span) g hg ⟨c, hc⟩
      have hmem : B.matOf (x : MulAut ↥B.span) ∈
          B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :=
        ⟨g, hgN0, B.acts_matOf hg⟩
      rwa [hN0] at hmem
  · exact hodd
  · obtain ⟨g, hgN, hgnot⟩ := SetLike.not_le_iff_exists.mp hfus.1
    refine ⟨⟨ggConjAut B.span hgN, ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hgN⟩, ?_⟩
    rintro ⟨c, hc⟩
    exact hgnot (hcond (ggConjAut B.span hgN) g (ggConjAut_apply B.span hgN) ⟨c, hc⟩)

end CFSG.StandardType.FrameRoute.FS81

end
