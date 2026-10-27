module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalHermitianBlock
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.RankThree.CentralLift

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.ClassicalGroups.Orthogonal (statedOmegaEquiv regular_quadOdd regular_quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry (elementaryIsometryEquiv)

variable {K : Type} [Field K]

theorem nonempty_statedOmegaOdd_mulEquiv_normTail (hK : ringChar K ≠ 2) {n : ℕ} (hn : 3 ≤ n) :
    ∃ T : NormTailData K K, (∀ z, normForm T z = z ^ 2) ∧
      Nonempty (StatedOmega (StatedQuadOdd n K) ≃*
        orthElementaryGroup (quadTail n (normForm T))) := by
  let T : NormTailData K K := ⟨AlgEquiv.refl, fun _ => rfl, fun z _ => ⟨z, rfl⟩⟩
  have hT : ∀ z, normForm T z = z ^ 2 := fun z => by
    have h := algebraMap_normForm T z
    change normForm T z = z * z at h
    rw [pow_two, h]
  let ι : (normForm T).IsometryEquiv (oddTailForm K) :=
    { toLinearEquiv := (LinearEquiv.funUnique Unit K K).symm
      map_app' := fun z => by
        rw [oddTailForm_apply, hT]
        rfl }
  let ψ : (quadTail n (normForm T)).IsometryEquiv (quadOdd n K) :=
    (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl (quadPlus n K)) ι).trans
      (oddTailIsometry n K)
  obtain ⟨hB, hT3⟩ := regular_quadOdd (Ring.two_ne_zero hK) hn
  have hE := orthogonal_odd_derived_elementary hK hB hT3
  exact ⟨T, hT, ⟨(statedOmegaEquiv (coe_quadOdd n K) hE).trans (elementaryIsometryEquiv ψ).symm⟩⟩

theorem nonempty_statedOmegaMinus_mulEquiv_normTail [Finite K] (hK : ringChar K ≠ 2) {n : ℕ}
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (T : NormTailData K L),
      Module.finrank K L = 2 ∧
      (∃ e : L ≃ₗ[K] (Fin 2 → K), ∀ z, normForm T z = e z 0 ^ 2 + b * e z 0 * e z 1 +
        c * e z 1 ^ 2) ∧
      Nonempty (StatedOmega (StatedQuadMinus n K b c) ≃*
        orthElementaryGroup (quadTail (n - 1) (normForm T))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fact (∀ r : K, r ^ 2 ≠ -c + b * r) := ⟨fun r h => hirr (-r) (by linear_combination h)⟩
  let T : NormTailData K (QuadraticAlgebra K (-c) b) :=
    { bar := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by ext <;> simp
      bar_bar := fun z => star_star z
      exists_eq_of_bar_eq := fun z hz => by
        refine ⟨z.re, ?_⟩
        have him : z.im = 0 := by
          have h := congrArg QuadraticAlgebra.im hz
          change -z.im = z.im at h
          have h' : 2 * z.im = 0 := by linear_combination -h
          exact (mul_eq_zero.1 h').resolve_left h2
        rw [QuadraticAlgebra.algebraMap_eq]
        ext
        · rfl
        · exact him.symm }
  have hN : ∀ z, normForm T z = z.re ^ 2 + b * z.re * z.im + c * z.im ^ 2 := fun z => by
    have h := algebraMap_normForm T z
    change _ = z * star z at h
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star] at h
    rw [(algebraMap K (QuadraticAlgebra K (-c) b)).injective h, QuadraticAlgebra.norm_def]
    ring
  let ι : (normForm T).IsometryEquiv (minusTailForm K b c) :=
    { toLinearEquiv := QuadraticAlgebra.linearEquivTuple (-c) b
      map_app' := fun z => by
        rw [minusTailForm_apply, hN]
        simp }
  let ψ : (quadTail (n - 1) (normForm T)).IsometryEquiv (quadMinus n K b c) :=
    (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl (quadPlus (n - 1) K)) ι).trans
      (minusTailIsometry n K b c)
  obtain ⟨hB, hT3⟩ := regular_quadMinus hn hirr
  have hE := orthogonal_odd_derived_elementary hK hB hT3
  exact ⟨QuadraticAlgebra K (-c) b, inferInstance, inferInstance, T,
    QuadraticAlgebra.finrank_eq_two _ _, ⟨QuadraticAlgebra.linearEquivTuple (-c) b, fun z => by
      rw [hN]
      simp⟩,
    ⟨(statedOmegaEquiv (coe_quadMinus n K b c) hE).trans (elementaryIsometryEquiv ψ).symm⟩⟩

end CFSG.RankThree.CentralLift
