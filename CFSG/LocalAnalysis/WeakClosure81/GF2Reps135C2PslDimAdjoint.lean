module

public import CFSG.LieType.SpecialLinear.ExteriorModel.AdjointHeart

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.GuralnickMalle

private lemma c2sldad_natCast_three (k : Type) [Field k] [CharP k 2] : ((3 : ℕ) : k) = 1 := by
  rw [CharTwo.natCast_eq_ite, if_neg (by decide : ¬ Even 3)]

private lemma c2sldad_trace_one_fin_three (k : Type) [Field k] [CharP k 2] :
    Matrix.trace (1 : Matrix (Fin 3) (Fin 3) k) = 1 := by
  rw [Matrix.trace_one, Fintype.card_fin, c2sldad_natCast_three k]

private lemma c2sldad_finrank_slMatrices_three (k : Type) [Field k] [CharP k 2] :
    finrank k (slMatrices 3 k) = 8 := by
  have hrange : LinearMap.range (Matrix.traceLinearMap (Fin 3) k k) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨c • (1 : Matrix (Fin 3) (Fin 3) k), ?_⟩
    change Matrix.trace (c • (1 : Matrix (Fin 3) (Fin 3) k)) = c
    rw [Matrix.trace_smul, c2sldad_trace_one_fin_three k]
    simp
  have hker : finrank k (LinearMap.ker (Matrix.traceLinearMap (Fin 3) k k)) = 8 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 3) k k)
    rw [hrange, finrank_top, Module.finrank_self] at hrn
    have hmat : finrank k (Matrix (Fin 3) (Fin 3) k) = 9 := by
      rw [Module.finrank_matrix]
      norm_num
    omega
  rwa [slMatrices]

private lemma c2sldad_slScalars_three_eq_bot (k : Type) [Field k] [CharP k 2] :
    slScalars 3 k = ⊥ := by
  have h1 : (1 : Matrix (Fin 3) (Fin 3) k) ∉ slMatrices 3 k := by
    intro hmem
    have h := hmem
    change (1 : Matrix (Fin 3) (Fin 3) k) ∈
      LinearMap.ker (Matrix.traceLinearMap (Fin 3) k k) at h
    rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply] at h
    rw [c2sldad_trace_one_fin_three k] at h
    exact one_ne_zero h
  have hdisj : Disjoint (slMatrices 3 k)
      (Submodule.span k {(1 : Matrix (Fin 3) (Fin 3) k)}) :=
    Submodule.disjoint_span_singleton_of_notMem h1
  have hcomap := Submodule.disjoint_iff_comap_eq_bot.mp hdisj
  simpa [slScalars] using hcomap

private lemma c2sldad_finrank_slScalars_three (k : Type) [Field k] [CharP k 2] :
    finrank k (slScalars 3 k) = 0 := by
  rw [c2sldad_slScalars_three_eq_bot k, finrank_bot]

private lemma c2sldad_finrank_adjointHeart_three (k : Type) [Field k] [CharP k 2] :
    finrank k (AdjointHeart 3 k) = 8 := by
  change finrank k (slMatrices 3 k ⧸ slScalars 3 k) = 8
  have hq := Submodule.finrank_quotient_add_finrank (R := k) (M := slMatrices 3 k)
    (slScalars 3 k)
  rw [c2sldad_finrank_slScalars_three k, c2sldad_finrank_slMatrices_three k] at hq
  simpa using hq

theorem w135c2_finrank_bModel_adjoint_three {k : Type} [Field k] [CharP k 2]
    (ε : Fin 1 → Finset (Fin 3)) (a b : Fin 3) (ha : (a : ℕ) = 1) (hb : (b : ℕ) = 2)
    (hε : ∀ r, ε r = {a, b}) : finrank k (BModel k ε) = 8 := by
  have ha' : a = ⟨1, by omega⟩ := Fin.ext ha
  have hb' : b = ⟨2, by omega⟩ := Fin.ext hb
  have hε0 : ε 0 = {⟨1, by omega⟩, ⟨2, by omega⟩} := by
    rw [hε 0, ha', hb']
  obtain ⟨Φ, -⟩ := exists_bModel_equiv_adjointHeart (k := k) (n := 3) (τ := Fin 1)
    le_rfl ε 0 hε0 (fun r hr => absurd (Subsingleton.elim r 0) hr)
  rw [LinearEquiv.finrank_eq Φ]
  exact c2sldad_finrank_adjointHeart_three k

end CFSG.LocalAnalysis.WeakClosure81
