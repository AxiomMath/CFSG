module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrixSemilinearAction
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrix

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.Universal
  CFSG.LieType.RootSystem
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.AUTSL

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

theorem ggRootNormInner_spinPlus_four_of_not_semilinear {F : Type} [Field F] [Finite F]
    [CharP F 2] {β : Fin (Spin.plusDatum 4 F (by norm_num)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum 4 F (by norm_num)).roots)
    (u : ↥(spinGroup (Spin.quadPlus 4 F)))
    {y : MulAut ↥(spinGroup (Spin.quadPlus 4 F))} (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    (htriv : GGTrivialOnNormalizer
      (((Spin.plusDatum 4 F (by norm_num)).rootGroup β).map (MulAut.conj u).toMonoidHom) y)
    (_hnot : ¬ ∃ (A : GL (Fin 4 ⊕ Fin 4) F) (φ : F ≃+* F) (μ : Fˣ),
      GGSemilinearSimilitude (Spin.quadPlus 4 F) A φ μ ∧
        GGMatrixSemilinearAction (Spin.quadPlus 4 F) A φ μ y) :
    ∃ k : ↥(spinGroup (Spin.quadPlus 4 F)), y = MulAut.conj k := by
  obtain ⟨m, hm⟩ := hy2
  obtain ⟨j, A, φ, μ, hsim, hmat⟩ :=
    exists_semilinear_similitude_of_triality_conj y m hm
  set τ : MulAut ↥(spinGroup (Spin.quadPlus 4 F)) :=
    (triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j with hτ
  set yj : MulAut ↥(spinGroup (Spin.quadPlus 4 F)) := τ * y * τ⁻¹ with hyj
  have hy2j : ∃ k : ℕ, yj ^ 2 ^ k = 1 := by
    refine ⟨m, ?_⟩
    have hyj' : yj = MulAut.conj τ y := by
      rw [hyj, hτ]
      rfl
    rw [hyj', ← map_pow, hm, map_one]
  have htrivj : GGTrivialOnNormalizer
      (((Spin.plusDatum 4 F (by norm_num)).rootGroup ((tri^[j]) β)).map
        (MulAut.conj (τ u)).toMonoidHom) yj := by
    have h1 := ggTrivialOnNormalizer_conj
      (((Spin.plusDatum 4 F (by norm_num)).rootGroup β).map (MulAut.conj u).toMonoidHom) y τ htriv
    rw [hyj, hτ]
    rw [hτ] at h1
    rw [map_triSpinAut_conj_rootGroup hβ u j] at h1
    exact h1
  have hβj : ((tri^[j]) β) ∈ (Spin.plusDatum 4 F (by norm_num)).roots :=
    tri_iterate_mem_roots hβ j
  obtain ⟨k, hk⟩ := ggRootNormInner_semilinear_plus (n := 4) (by norm_num) hβj (τ u)
    A φ μ hsim yj hy2j htrivj hmat
  refine ⟨τ⁻¹ k, ?_⟩
  rw [hyj] at hk
  have h2 : y = τ⁻¹ * MulAut.conj k * τ := by
    rw [← hk]; group
  rw [h2]
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

end CFSG.StandardType.LieKnownR2.POmega.Inner
