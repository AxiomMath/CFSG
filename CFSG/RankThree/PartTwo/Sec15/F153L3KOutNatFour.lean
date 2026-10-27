module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatE

open Matrix

lemma two_eq_zero_aux (K : Type) [Field K] [CharP K 2] : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

lemma exists_omega_aux {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  classical
  have hx : ∃ x : F, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro x _
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp [h x hx0]
    have h1 := Finset.card_le_card hsub
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, hF] at h1
    omega
  obtain ⟨x, hx0, hx1⟩ := hx
  have h4 : x ^ 4 = x := by
    have h := FiniteField.pow_card x
    rw [hF] at h
    exact h
  have h3 : x ^ 3 = 1 := by
    have h : x * (x ^ 3 - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hx0
    · exact sub_eq_zero.mp h
  refine ⟨x, hx0, hx1, ?_⟩
  have h : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hx1
  · exact h

lemma mem_cube_roots_aux {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (c : F) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  have h4 : c ^ 4 = c := by
    have h := FiniteField.pow_card c
    rw [hF] at h
    exact h
  have hc3 : c ^ 3 = 1 := by
    have h : c * (c ^ 3 - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc
    · exact sub_eq_zero.mp h
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h : (c - 1) * (c - ω) * (c - ω ^ 2) = 0 := by
    linear_combination hc3 + (c - c ^ 2) * hω + (c - 1) * hω3
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

lemma matrix_eq_of_mulVec_aux {K : Type} [CommRing K] {M N : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ v : Fin 3 → K, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have h' := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h'

theorem eq_matrix_of_card_four {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : Fintype.card F = 4)
    {a : (Fin 3 → F) ≃+ (Fin 3 → F)} (ha : ∀ u, a (a u) = u)
    (hnorm : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F, ∃ s' : Matrix.SpecialLinearGroup (Fin 3) F,
      ∀ u, a ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ u) = (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ a u)
    (hrank : (Set.range fun u => a u - u).ncard ≤ 4) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 3) F, ∀ u, a u = (M : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
  obtain ⟨ω, _hω0, hω1, hω⟩ := exists_omega_aux hF
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h2 : (2 : F) = 0 := two_eq_zero_aux F
  have hdet : (ω • (1 : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hω3]
  obtain ⟨z, hz_def⟩ : ∃ z : Matrix.SpecialLinearGroup (Fin 3) F,
      (z : Matrix (Fin 3) (Fin 3) F) = ω • (1 : Matrix (Fin 3) (Fin 3) F) :=
    ⟨⟨ω • (1 : Matrix (Fin 3) (Fin 3) F), hdet⟩, rfl⟩
  have hz : ∀ u : Fin 3 → F, (z : Matrix (Fin 3) (Fin 3) F) *ᵥ u = ω • u := by
    intro u
    rw [hz_def, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨s', hs'⟩ := hnorm z
  have hA : ∀ u, a (ω • u) = (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ a u := by
    intro u
    have h := hs' u
    rwa [hz u] at h
  have hsv : ∀ v, (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ v = a (ω • a v) := by
    intro v
    have h := hA (a v)
    rw [ha] at h
    exact h.symm
  have hcomm : ∀ y : Matrix.SpecialLinearGroup (Fin 3) F,
      (s' : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F)
        = (y : Matrix (Fin 3) (Fin 3) F) * (s' : Matrix (Fin 3) (Fin 3) F) := by
    intro y
    obtain ⟨y', hy'⟩ := hnorm y
    have hy : ∀ v, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v
        = a ((y' : Matrix (Fin 3) (Fin 3) F) *ᵥ a v) := by
      intro v
      rw [← hy' v, ha]
    apply matrix_eq_of_mulVec_aux
    intro w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsv (y *ᵥ w), hy w, ha (y' *ᵥ a w),
      hy (s' *ᵥ w), hsv w, ha (ω • a w), Matrix.mulVec_smul]
  have hcen : s' ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact (hcomm g).symm)
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  rw [Fintype.card_fin] at hr3
  have hrS : ∀ v : Fin 3 → F, (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ v = r • v := by
    intro v
    rw [← hr, Matrix.scalar_apply]
    funext i
    simp [Matrix.mulVec_diagonal]
  have hAr : ∀ u : Fin 3 → F, a (ω • u) = r • a u := by
    intro u
    rw [hA u, hrS]
  have hrω : r = ω := by
    rcases mem_cube_roots_aux hF hω r with h | h | h | h
    · exfalso
      rw [h] at hr3
      norm_num at hr3
    · exfalso
      rw [h] at hAr
      have h1 : ∀ u : Fin 3 → F, ω • u = u := fun u => a.injective (by rw [hAr u, one_smul])
      have h2' := congrFun (h1 (fun _ => 1)) 0
      simp at h2'
      exact hω1 h2'
    · exact h
    · exfalso
      rw [h] at hAr
      have hA2 : ∀ u : Fin 3 → F, a ((ω ^ 2) • u) = ω • a u := by
        intro u
        have e : (ω ^ 2) • u = ω • (ω • u) := by rw [smul_smul, pow_two]
        have hmul : ω ^ 2 * ω ^ 2 = ω := by linear_combination ω * hω3
        rw [e, hAr (ω • u), hAr u, smul_smul, hmul]
      have hc : ∀ u : Fin 3 → F, a (ω • a ((ω ^ 2) • u)) = ω • u := by
        intro u
        rw [hA2 u, smul_smul, ← pow_two, hA2 (a u), ha]
      have hωω2 : ∀ u : Fin 3 → F, ω • (ω ^ 2) • u = u := by
        intro u
        rw [smul_smul, show ω * ω ^ 2 = 1 by linear_combination hω3, one_smul]
      have key : ∀ u : Fin 3 → F, a (ω • a ((ω ^ 2) • u)) - u
          = (a u - u) + a (ω • (a ((ω ^ 2) • u) - (ω ^ 2) • u)) := by
        intro u
        rw [smul_sub, hωω2 u, map_sub]
        abel
      obtain ⟨t, ht⟩ : ∃ t : F, (ω - 1) * t = 1 :=
        ⟨(ω - 1)⁻¹, mul_inv_cancel₀ (sub_ne_zero.mpr hω1)⟩
      have hsub : (Set.univ : Set (Fin 3 → F)) ⊆
          (fun p : (Fin 3 → F) × (Fin 3 → F) => p.1 + a (ω • p.2)) ''
            (Set.range (fun u => a u - u) ×ˢ Set.range (fun u => a u - u)) := by
        intro v _
        have hu : ω • (t • v) - t • v = v := by
          rw [smul_smul, ← sub_smul, show ω * t - t = 1 by linear_combination ht, one_smul]
        refine ⟨(a (t • v) - t • v, a ((ω ^ 2) • (t • v)) - (ω ^ 2) • (t • v)),
          ⟨⟨t • v, rfl⟩, ⟨(ω ^ 2) • (t • v), rfl⟩⟩, ?_⟩
        show (a (t • v) - t • v) + a (ω • (a ((ω ^ 2) • (t • v)) - (ω ^ 2) • (t • v))) = v
        rw [← key (t • v), hc (t • v)]
        exact hu
      have hU : (Set.univ : Set (Fin 3 → F)).ncard = 64 := by
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, hF]
      have hle1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hle2 : ((fun p : (Fin 3 → F) × (Fin 3 → F) => p.1 + a (ω • p.2)) ''
            (Set.range (fun u => a u - u) ×ˢ Set.range (fun u => a u - u))).ncard
          ≤ (Set.range (fun u => a u - u) ×ˢ Set.range (fun u => a u - u)).ncard :=
        Set.ncard_image_le (Set.toFinite _)
      have hle3 : (Set.range (fun u => a u - u) ×ˢ Set.range (fun u => a u - u)).ncard ≤ 16 := by
        rw [Set.ncard_prod]
        exact (Nat.mul_le_mul hrank hrank).trans (by norm_num)
      have hfin := hle1.trans (hle2.trans hle3)
      rw [hU] at hfin
      norm_num at hfin
  have hA1 : ∀ u : Fin 3 → F, a (ω • u) = ω • a u := fun u => by rw [hAr u, hrω]
  have hA1' : ∀ u : Fin 3 → F, a ((ω ^ 2) • u) = (ω ^ 2) • a u := by
    intro u
    have e : (ω ^ 2) • u = ω • (ω • u) := by rw [smul_smul, pow_two]
    rw [e, hA1, hA1, smul_smul, ← pow_two]
  have hAc : ∀ (c : F) (u : Fin 3 → F), a (c • u) = c • a u := by
    intro c u
    rcases mem_cube_roots_aux hF hω c with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      simp
    · rw [h]
      exact hA1 u
    · rw [h]
      exact hA1' u
  obtain ⟨A, hAa⟩ : ∃ A : (Fin 3 → F) →ₗ[F] (Fin 3 → F), ∀ u, A u = a u :=
    ⟨{ toFun := a
       map_add' := fun x y => map_add a x y
       map_smul' := fun c x => by simp [hAc c x] }, fun u => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F, ∀ u, a u = M *ᵥ u :=
    ⟨LinearMap.toMatrix' A, fun u => by rw [← hAa u, LinearMap.toMatrix'_mulVec]⟩
  have hMM : M * M = 1 := by
    apply matrix_eq_of_mulVec_aux
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ← hM (M *ᵥ v), ← hM v, ha]
  have hdetM : M.det = 1 := by
    have h1 : M.det * M.det = 1 := by
      rw [← Matrix.det_mul, hMM, Matrix.det_one]
    have h3 : (M.det - 1) * (M.det - 1) = 0 := by
      linear_combination h1 + (1 - M.det) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  exact ⟨⟨M, hdetM⟩, fun u => hM u⟩

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatE
