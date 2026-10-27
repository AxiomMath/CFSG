module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open LinearMap

theorem w16g_isotropic_weight (v : Fin 4 → ZMod 3) (hv : v ⬝ᵥ v = 0) :
    v = 0 ∨ Fintype.card {i : Fin 4 // v i ≠ 0} = 3 :=
  (by decide : ∀ v : Fin 4 → ZMod 3, v ⬝ᵥ v = 0 →
      v = 0 ∨ Fintype.card {i : Fin 4 // v i ≠ 0} = 3) v hv

theorem w16g_weight_of_selfOrthogonal (v : Fin 4 → ZMod 3) (hv : v ⬝ᵥ v = 0) (hv0 : v ≠ 0) :
    Fintype.card {i : Fin 4 // v i ≠ 0} = 3 := by
  rcases w16g_isotropic_weight v hv with h | h
  · exact absurd h hv0
  · exact h

theorem w16g_selfDual_of_totallyIsotropic (S : Submodule (ZMod 3) (Fin 4 → ZMod 3))
    (hS : S ≤ ((1 : Matrix (Fin 4) (Fin 4) (ZMod 3)).toBilin').orthogonal S)
    (hfr : Module.finrank (ZMod 3) S = 2) :
    ((1 : Matrix (Fin 4) (Fin 4) (ZMod 3)).toBilin').orthogonal S = S := by
  set B := (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)).toBilin' with hBdef
  have hBnd : B.Nondegenerate := by
    rw [hBdef]
    exact Matrix.nondegenerate_toBilin'_iff.mpr (by
      rw [Matrix.nondegenerate_iff_det_ne_zero]
      simp)
  have hfr' : Module.finrank (ZMod 3) S =
      Module.finrank (ZMod 3) ↥(B.orthogonal S) := by
    rw [hfr, LinearMap.BilinForm.finrank_orthogonal hBnd S, hfr]
    norm_num
  exact (Submodule.eq_of_le_of_finrank_eq hS hfr').symm

theorem w16g_core (qv rv y : Fin 4 → ZMod 3)
    (hq0 : qv 0 ≠ 0) (hq1 : qv 1 ≠ 0) (hq2 : qv 2 ≠ 0) (hq3 : qv 3 = 0)
    (hr0 : rv 0 ≠ 0) (hr1 : rv 1 ≠ 0) (hr2 : rv 2 = 0) (hr3 : rv 3 ≠ 0)
    (horth : qv ⬝ᵥ rv = 0) (hy1 : qv ⬝ᵥ y = 0) (hy2 : rv ⬝ᵥ y = 0) :
    y ∈ Submodule.span (ZMod 3) ({qv, rv} : Set (Fin 4 → ZMod 3)) := by
  set B := (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)).toBilin' with hBdef
  have hB : ∀ u v : Fin 4 → ZMod 3, B u v = u ⬝ᵥ v := by
    intro u v
    rw [hBdef, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hqq : qv ⬝ᵥ qv = 0 := by
    have hdec : ∀ a b c : ZMod 3, a ≠ 0 → b ≠ 0 → c ≠ 0 →
        (![a, b, c, 0] : Fin 4 → ZMod 3) ⬝ᵥ ![a, b, c, 0] = 0 := by decide
    have hqv : qv = ![qv 0, qv 1, qv 2, qv 3] := by
      funext i; fin_cases i <;> rfl
    rw [hqv, hq3]
    exact hdec (qv 0) (qv 1) (qv 2) hq0 hq1 hq2
  have hrr : rv ⬝ᵥ rv = 0 := by
    have hdec : ∀ a b c : ZMod 3, a ≠ 0 → b ≠ 0 → c ≠ 0 →
        (![a, b, 0, c] : Fin 4 → ZMod 3) ⬝ᵥ ![a, b, 0, c] = 0 := by decide
    have hrv : rv = ![rv 0, rv 1, rv 2, rv 3] := by
      funext i; fin_cases i <;> rfl
    rw [hrv, hr2]
    exact hdec (rv 0) (rv 1) (rv 3) hr0 hr1 hr3
  have hrq : rv ⬝ᵥ qv = 0 := by rw [dotProduct_comm]; exact horth
  set S := Submodule.span (ZMod 3) ({qv, rv} : Set (Fin 4 → ZMod 3)) with hSdef
  have hqv_orth : qv ∈ B.orthogonal S := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hSdef, Submodule.mem_span_pair] at hn
    obtain ⟨p, q, rfl⟩ := hn
    rw [hB]
    simp only [add_dotProduct, smul_dotProduct, hqq, hrq, smul_zero, add_zero]
  have hrv_orth : rv ∈ B.orthogonal S := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hSdef, Submodule.mem_span_pair] at hn
    obtain ⟨p, q, rfl⟩ := hn
    rw [hB]
    simp only [add_dotProduct, smul_dotProduct, horth, hrr, smul_zero, add_zero]
  have hSle : S ≤ B.orthogonal S := by
    rw [hSdef, Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hqv_orth
    · rw [hx]; exact hrv_orth
  have hfr : Module.finrank (ZMod 3) S = 2 := by
    have hli : LinearIndependent (ZMod 3) ![(qv : Fin 4 → ZMod 3), rv] := by
      rw [LinearIndependent.pair_iff]
      intro p q hpq
      constructor
      · have h2 : p * qv 2 = 0 := by
          have h := congrFun hpq 2
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
          rwa [hr2, mul_zero, add_zero] at h
        exact (mul_eq_zero.mp h2).resolve_right hq2
      · have h3 : q * rv 3 = 0 := by
          have h := congrFun hpq 3
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
          rwa [hq3, mul_zero, zero_add] at h
        exact (mul_eq_zero.mp h3).resolve_right hr3
    have hrange : Set.range ![(qv : Fin 4 → ZMod 3), rv] =
        ({qv, rv} : Set (Fin 4 → ZMod 3)) := by
      ext x
      simp [eq_comm]
      tauto
    rw [hSdef, ← hrange, finrank_span_eq_card hli]
    simp
  have heq := w16g_selfDual_of_totallyIsotropic S hSle hfr
  have hyorth : y ∈ B.orthogonal S := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hSdef, Submodule.mem_span_pair] at hn
    obtain ⟨p, q, rfl⟩ := hn
    rw [hB]
    simp only [add_dotProduct, smul_dotProduct, hy1, hy2, smul_zero, add_zero]
  rwa [heq] at hyorth

end CFSG.LocalAnalysis.WeakClosure81
