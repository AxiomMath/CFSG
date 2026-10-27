module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroSubmodule

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm spForm_apply spForm_isAlt spForm_mulVec)

variable {F : Type} [Field F] {r : ℕ}

private lemma spForm_swap (x y : Fin r ⊕ Fin r → F) :
    spForm r F y x = - spForm r F x y :=
  (spForm_isAlt (r := r) (K := F)).neg_eq x y |>.symm

private lemma dotProduct_mulVec_transpose {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    (v w : Fin r ⊕ Fin r → F) :
    (M *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Mᵀ *ᵥ w) := by
  rw [← Matrix.vecMul_transpose M v, ← Matrix.dotProduct_mulVec]

private lemma spForm_mulVec_of_isometry {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    (hA : Aᵀ * formJ r F * A = formJ r F) (x y : Fin r ⊕ Fin r → F) :
    spForm r F (A *ᵥ x) (A *ᵥ y) = spForm r F x y := by
  rw [spForm_mulVec]
  rw [show CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F r = formJ r F from rfl, hA]
  rfl

private lemma spForm_mulVec_of_similitude {B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {ν : F} (hB : Bᵀ * formJ r F * B = ν • formJ r F) (x y : Fin r ⊕ Fin r → F) :
    spForm r F (B *ᵥ x) (B *ᵥ y) = ν * spForm r F x y := by
  rw [spForm_mulVec]
  rw [show CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F r = formJ r F from rfl, hB,
    Matrix.toBilin'_apply', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, spForm_apply]
  rfl


private lemma spForm_apply_adjoint {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {c : F}
    (hc : c = 1 ∨ c = -1) (hM : Mᵀ * formJ r F = c • (formJ r F * M))
    (x y : Fin r ⊕ Fin r → F) :
    spForm r F x (M *ᵥ y) = c * spForm r F (M *ᵥ x) y := by
  have hc2 : c * c = 1 := by rcases hc with h | h <;> rw [h] <;> ring
  have hJM : formJ r F * M = c • (Mᵀ * formJ r F) := by
    have h := congrArg (fun X => c • X) hM
    rw [smul_smul, hc2, one_smul] at h
    exact h.symm
  rw [spForm_apply, spForm_apply,
    show CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F r = formJ r F from rfl]
  rw [Matrix.mulVec_mulVec, hJM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Matrix.mulVec_mulVec, dotProduct_mulVec_transpose]

private lemma transpose_smul_one_mul_formJ (c : F) :
    (c • 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ * formJ r F * (c • 1) =
      (c * c) • formJ r F := by
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul]

private lemma spForm_span_eq_zero {S : Set (Fin r ⊕ Fin r → F)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, spForm r F x y = 0) :
    ∀ x ∈ Submodule.span F S, ∀ y ∈ Submodule.span F S, spForm r F x y = 0 := by
  intro x hx y hy
  have hgen : ∀ s ∈ S, spForm r F s y = 0 := by
    intro s hs
    have hle : Submodule.span F S ≤ LinearMap.ker (spForm r F s) := by
      rw [Submodule.span_le]
      intro t ht
      exact hS s hs t ht
    exact hle hy
  have hle : Submodule.span F S ≤ LinearMap.ker (spForm r F y) := by
    rw [Submodule.span_le]
    intro s hs
    change ((spForm r F y)) s = 0
    rw [spForm_swap s y, hgen s hs, neg_zero]
  have h0 : spForm r F y x = 0 := hle hx
  rw [spForm_swap y x, h0, neg_zero]

private lemma mulVec_mem_span {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {S : Set (Fin r ⊕ Fin r → F)}
    (hS : ∀ s ∈ S, M *ᵥ s ∈ Submodule.span F S) :
    ∀ w ∈ Submodule.span F S, M *ᵥ w ∈ Submodule.span F S := by
  set W : Submodule F (Fin r ⊕ Fin r → F) := Submodule.span F S with hW
  have hle : W ≤ W.comap (Matrix.toLin' M) := by
    rw [hW, Submodule.span_le]
    intro s hs
    change Matrix.toLin' M s ∈ W
    rw [Matrix.toLin'_apply]
    exact hS s hs
  intro w hw
  have h := hle hw
  change Matrix.toLin' M w ∈ W at h
  rw [Matrix.toLin'_apply] at h
  exact h

private lemma mem_ker_sub_iff {M N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {x : Fin r ⊕ Fin r → F} :
    x ∈ LinearMap.ker (Matrix.toLin' (M - N)) ↔ M *ᵥ x = N *ᵥ x := by
  change Matrix.toLin' (M - N) x = 0 ↔ M *ᵥ x = N *ᵥ x
  rw [Matrix.toLin'_apply, Matrix.sub_mulVec, sub_eq_zero]

private lemma mem_ker_sub_one_iff {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {x : Fin r ⊕ Fin r → F} :
    x ∈ LinearMap.ker (Matrix.toLin' (A - 1)) ↔ A *ᵥ x = x := by
  rw [mem_ker_sub_iff, Matrix.one_mulVec]

private lemma mem_ker_add_one_iff {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {x : Fin r ⊕ Fin r → F} :
    x ∈ LinearMap.ker (Matrix.toLin' (A + 1)) ↔ A *ᵥ x = -x := by
  change Matrix.toLin' (A + 1) x = 0 ↔ A *ᵥ x = -x
  rw [Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg]

private lemma ker_sub_ne_bot_of_mul_eq {M N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    (hcomm : M * N = N * M) (hsq : M * M = N * N) (hM : M ≠ -N) :
    LinearMap.ker (Matrix.toLin' (M - N)) ≠ ⊥ := by
  intro hker
  obtain hzero := Matrix.ker_toLin'_eq_bot_iff.mp hker
  have hprod : (M - N) * (M + N) = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, hcomm, hsq]
    abel
  have hsum : M + N = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    have hy : (M - N) *ᵥ ((M + N) *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, hprod, Matrix.zero_mulVec]
    have h0 := hzero ((M + N) *ᵥ x) hy
    simpa using h0
  exact hM (eq_neg_iff_add_eq_zero.mpr hsum)

private lemma exists_eigenspace_finrank_ge {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    (h2 : (2 : F) ≠ 0) (hAA : A * A = 1) :
    ∃ U : Submodule F (Fin r ⊕ Fin r → F),
      (U = LinearMap.ker (Matrix.toLin' (A - 1)) ∨
        U = LinearMap.ker (Matrix.toLin' (A + 1))) ∧ r ≤ Module.finrank F U := by
  set Vp : Submodule F (Fin r ⊕ Fin r → F) := LinearMap.ker (Matrix.toLin' (A - 1)) with hVp
  set Vm : Submodule F (Fin r ⊕ Fin r → F) := LinearMap.ker (Matrix.toLin' (A + 1)) with hVm
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hAx : A *ᵥ (A *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
    have hx : x = (2 : F)⁻¹ • (x + A *ᵥ x) + (2 : F)⁻¹ • (x - A *ᵥ x) := by
      rw [← smul_add, show x + A *ᵥ x + (x - A *ᵥ x) = (2 : F) • x by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [hVp, mem_ker_sub_one_iff, Matrix.mulVec_smul, Matrix.mulVec_add, hAx, add_comm]
    · rw [hVm, mem_ker_add_one_iff, Matrix.mulVec_smul, Matrix.mulVec_sub, hAx,
        ← neg_sub x (A *ᵥ x), smul_neg]
  have hle : Module.finrank F ↥(Vp ⊔ Vm) ≤ Module.finrank F ↥Vp + Module.finrank F ↥Vm :=
    Submodule.finrank_add_le_finrank_add_finrank Vp Vm
  rw [hsup, finrank_top F (Fin r ⊕ Fin r → F), Module.finrank_fintype_fun_eq_card F,
    Fintype.card_sum, Fintype.card_fin] at hle
  have hcase : r ≤ Module.finrank F ↥Vp ∨ r ≤ Module.finrank F ↥Vm := by omega
  rcases hcase with h | h
  · exact ⟨Vp, Or.inl hVp, h⟩
  · exact ⟨Vm, Or.inr hVm, h⟩

private lemma beta_eq_or_neg [NeZero r] {B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {ν β : F} (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hBB : B * B = β • 1)
    (hν : ¬ IsSquare ν) : ν ≠ 0 ∧ β ≠ 0 ∧ (β = ν ∨ β = -ν) := by
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact IsSquare.zero)
  have hβ2 : β * β = ν * ν := by
    have h1 : (B * B)ᵀ * formJ r F * (B * B) = (β * β) • formJ r F := by
      rw [hBB, transpose_smul_one_mul_formJ]
    have h2 : (B * B)ᵀ * formJ r F * (B * B) = (ν * ν) • formJ r F := by
      rw [mul_transpose_formJ_mul hB B, hB, smul_smul]
    exact smul_formJ_injective r (h1.symm.trans h2)
  have hβν : β = ν ∨ β = -ν := by
    have hfac : (β - ν) * (β + ν) = 0 := by linear_combination hβ2
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  refine ⟨hν0, ?_, hβν⟩
  rcases hβν with h | h
  · rw [h]; exact hν0
  · rw [h]; exact neg_ne_zero.mpr hν0

private lemma exists_sq_add_sq [Finite F] (h2 : (2 : F) ≠ 0) {α β : F} (hα : α ≠ 0)
    (hβ : β ≠ 0) (γ : F) : ∃ s t : F, α * s ^ 2 + β * t ^ 2 + γ = 0 := by
  classical
  have := Fintype.ofFinite F
  have hch : ringChar F ≠ 2 := fun h => h2 (by
    have := ringChar.spec F 2
    exact_mod_cast this.2 (by rw [h]))
  obtain ⟨s, t, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C γ)
    (g := Polynomial.C β * Polynomial.X ^ 2) (by compute_degree!) (by compute_degree!)
    (FiniteField.odd_card_of_char_ne_two hch)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  exact ⟨s, t, by linear_combination h⟩


theorem exists_isotropic_of_anticommute_of_eq {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) {r : ℕ} (hr : 2 ≤ r) {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {ν : F} (hA : Aᵀ * formJ r F * A = formJ r F) (hAA : A * A = -1)
    (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hν : ¬ IsSquare ν) (hBB : B * B = ν • 1)
    (hAB : A * B = -(B * A)) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  classical
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact IsSquare.zero)
  have hAadj : Aᵀ * formJ r F = -(formJ r F * A) := by
    have h := congrArg (fun M => M * A) hA
    rw [Matrix.mul_assoc, hAA, Matrix.mul_neg, Matrix.mul_one] at h
    exact neg_eq_iff_eq_neg.mp h
  have hBadj : Bᵀ * formJ r F = formJ r F * B := by
    have h1 : (Bᵀ * formJ r F * B) * B = (Bᵀ * formJ r F) * (B * B) := by
      simp only [Matrix.mul_assoc]
    have h2 : (Bᵀ * formJ r F) * (B * B) = ν • (Bᵀ * formJ r F) := by
      rw [hBB, Matrix.mul_smul, Matrix.mul_one]
    have h3 : ν • (Bᵀ * formJ r F) = ν • (formJ r F * B) := by
      have h0 := congrArg (fun M => M * B) hB
      rwa [h1, h2, Matrix.smul_mul] at h0
    have h' := congrArg (fun M => ν⁻¹ • M) h3
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hν0, one_smul, one_smul] at h'
    exact h'
  have hAadj' : Aᵀ * formJ r F = (-1 : F) • (formJ r F * A) := by
    rw [neg_one_smul]; exact hAadj
  have hBadj' : Bᵀ * formJ r F = (1 : F) • (formJ r F * B) := by
    rw [one_smul]; exact hBadj
  have hAω : ∀ x y, spForm r F x (A *ᵥ y) = - spForm r F (A *ᵥ x) y := by
    intro x y
    have := spForm_apply_adjoint (M := A) (c := -1) (Or.inr rfl) hAadj' x y
    simpa using this
  have hBω : ∀ x y, spForm r F x (B *ᵥ y) = spForm r F (B *ᵥ x) y := by
    intro x y
    have := spForm_apply_adjoint (M := B) (c := 1) (Or.inl rfl) hBadj' x y
    simpa using this
  have hBself : ∀ x, spForm r F x (B *ᵥ x) = 0 := by
    intro x
    have h1 := hBω x x
    have h2 := spForm_swap x (B *ᵥ x)
    rw [h2] at h1
    have htwo : (2 : F) * spForm r F x (B *ᵥ x) = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h1
    exact (mul_eq_zero.mp htwo).resolve_left h2F
  have hCself : ∀ x, spForm r F x ((A * B) *ᵥ x) = 0 := by
    intro x
    have hBA : B *ᵥ (A *ᵥ x) = -((A * B) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, show B * A = -(A * B) from by rw [hAB, neg_neg],
        Matrix.neg_mulVec]
    have h1 : spForm r F x (A *ᵥ (B *ᵥ x)) = - spForm r F (A *ᵥ x) (B *ᵥ x) :=
      hAω x (B *ᵥ x)
    have h2 : spForm r F (A *ᵥ x) (B *ᵥ x) = spForm r F x ((A * B) *ᵥ x) := by
      have h := hBω (A *ᵥ x) x
      rw [hBA] at h
      have h' : spForm r F (-((A * B) *ᵥ x)) x = - spForm r F ((A * B) *ᵥ x) x := by simp
      rw [h'] at h
      have h'' : spForm r F ((A * B) *ᵥ x) x =
          - spForm r F x ((A * B) *ᵥ x) := spForm_swap x ((A * B) *ᵥ x)
      rw [h''] at h
      rwa [neg_neg] at h
    have hAC : A *ᵥ (B *ᵥ x) = (A * B) *ᵥ x := by rw [Matrix.mulVec_mulVec]
    rw [hAC, h2] at h1
    have htwo : (2 : F) * spForm r F x ((A * B) *ᵥ x) = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h1
    exact (mul_eq_zero.mp htwo).resolve_left h2F
  have hcard : 3 ≤ Fintype.card (Fin r ⊕ Fin r) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨v, hv0, hvCW⟩ :=
    CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero hcard (formJ r F * A)
  have hvA : spForm r F v (A *ᵥ v) = 0 := by
    rw [spForm_apply, Matrix.mulVec_mulVec]
    rw [show CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F r = formJ r F from rfl]
    exact hvCW
  let S : Set (Fin r ⊕ Fin r → F) := {v, A *ᵥ v, B *ᵥ v, (A * B) *ᵥ v}
  have h12 : spForm r F (A *ᵥ v) (B *ᵥ v) = 0 := by
    rw [← spForm_mulVec_of_isometry hA (A *ᵥ v) (B *ᵥ v)]
    rw [Matrix.mulVec_mulVec, hAA, Matrix.neg_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
    have hneg : spForm r F (-v) ((A * B) *ᵥ v) = - spForm r F v ((A * B) *ᵥ v) := by simp
    rw [hneg, hCself v, neg_zero]
  have h13 : spForm r F (A *ᵥ v) ((A * B) *ᵥ v) = 0 := by
    rw [show (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) from by rw [Matrix.mulVec_mulVec]]
    rw [spForm_mulVec_of_isometry hA v (B *ᵥ v), hBself v]
  have hCv : (A * B) *ᵥ v = -(B *ᵥ (A *ᵥ v)) := by
    rw [show A * B = -(B * A) from by rw [hAB], Matrix.neg_mulVec,
      Matrix.mulVec_mulVec]
  have h23 : spForm r F (B *ᵥ v) ((A * B) *ᵥ v) = 0 := by
    calc spForm r F (B *ᵥ v) ((A * B) *ᵥ v)
        = spForm r F (B *ᵥ v) (-(B *ᵥ (A *ᵥ v))) := by rw [hCv]
      _ = - spForm r F (B *ᵥ v) (B *ᵥ (A *ᵥ v)) := by
          exact map_neg (spForm r F (B *ᵥ v)) (B *ᵥ (A *ᵥ v))
      _ = - (ν * spForm r F v (A *ᵥ v)) := by
          rw [spForm_mulVec_of_similitude hB v (A *ᵥ v)]
      _ = 0 := by rw [hvA, mul_zero, neg_zero]
  have hS : ∀ x ∈ S, ∀ y ∈ S, spForm r F x y = 0 := by
    intro x hx y hy
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy
    · rw [hx, hy]; exact spForm_isAlt.self_eq_zero v
    · rw [hx, hy]; exact hvA
    · rw [hx, hy]; exact hBself v
    · rw [hx, hy]; exact hCself v
    · rw [hx, hy, spForm_swap, hvA, neg_zero]
    · rw [hx, hy]; exact spForm_isAlt.self_eq_zero (A *ᵥ v)
    · rw [hx, hy]; exact h12
    · rw [hx, hy]; exact h13
    · rw [hx, hy, spForm_swap, hBself v, neg_zero]
    · rw [hx, hy, spForm_swap, h12, neg_zero]
    · rw [hx, hy]; exact spForm_isAlt.self_eq_zero (B *ᵥ v)
    · rw [hx, hy]; exact h23
    · rw [hx, hy, spForm_swap, hCself v, neg_zero]
    · rw [hx, hy, spForm_swap, h13, neg_zero]
    · rw [hx, hy, spForm_swap, h23, neg_zero]
    · rw [hx, hy]; exact spForm_isAlt.self_eq_zero ((A * B) *ᵥ v)
  refine ⟨Submodule.span F S, ?_, spForm_span_eq_zero hS, ?_, ?_⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, Submodule.subset_span (by simp [S]), hv0⟩
  · refine mulVec_mem_span ?_
    intro s hs
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp [S])
    · rw [Matrix.mulVec_mulVec, hAA, Matrix.neg_mulVec, Matrix.one_mulVec]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp [S]))
    · rw [Matrix.mulVec_mulVec]
      exact Submodule.subset_span (by simp [S])
    · rw [Matrix.mulVec_mulVec, show A * (A * B) = -B from by
        rw [← Matrix.mul_assoc, hAA, Matrix.neg_mul, Matrix.one_mul],
        Matrix.neg_mulVec]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp [S]))
  · refine mulVec_mem_span ?_
    intro s hs
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp [S])
    · rw [Matrix.mulVec_mulVec, show B * A = -(A * B) from by rw [hAB, neg_neg],
        Matrix.neg_mulVec]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp [S]))
    · rw [Matrix.mulVec_mulVec, hBB, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
    · rw [Matrix.mulVec_mulVec, show B * (A * B) = -(ν • A) from by
        rw [← Matrix.mul_assoc, show B * A = -(A * B) from by rw [hAB, neg_neg],
          Matrix.neg_mul, Matrix.mul_assoc, hBB, Matrix.mul_smul, Matrix.mul_one],
        Matrix.neg_mulVec, Matrix.smul_mulVec]
      exact Submodule.neg_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S])))


theorem exists_isotropic_of_anticommute {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    {r : ℕ} (hr : 3 ≤ r) {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {ε ν β : F}
    (hA : Aᵀ * formJ r F * A = formJ r F) (hAA : A * A = ε • 1) (hε : ε = 1 ∨ ε = -1)
    (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hν : ¬ IsSquare ν) (hBB : B * B = β • 1)
    (hAB : A * B = -(B * A)) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  classical
  have : NeZero r := ⟨by omega⟩
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨hν0, hβ0, hβν⟩ := beta_eq_or_neg (r := r) hB hBB hν
  rcases hε with hε1 | hεm1
  ·
    have hAA1 : A * A = 1 := by rw [hε1] at hAA; simpa using hAA
    have hAne : A ≠ -1 := by
      intro hAneg
      have hB0 : B = 0 := by
        have h1 : A * B = -B := by rw [hAneg, Matrix.neg_mul, Matrix.one_mul]
        have h2' : B * A = -B := by rw [hAneg, Matrix.mul_neg, Matrix.mul_one]
        have hBA : B * A = -(A * B) := by rw [hAB, neg_neg]
        have h3 : B = -B := by
          rw [hBA, h1] at h2'
          simpa using h2'
        have h4 : (2 : F) • B = 0 := by
          rw [two_smul]
          nth_rewrite 2 [h3]
          rw [add_neg_cancel]
        exact (smul_eq_zero.mp h4).resolve_left h2F
      have hν0' : ν = 0 := by
        have h := hB
        rw [hB0] at h
        simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero] at h
        have h0 : ν • formJ r F = (0 : F) • formJ r F := by
          rw [h.symm]
          exact (zero_smul F (formJ r F)).symm
        exact smul_formJ_injective r h0
      exact hν (by rw [hν0']; exact IsSquare.zero)
    have hK : LinearMap.ker (Matrix.toLin' (A - 1)) ≠ ⊥ :=
      ker_sub_ne_bot_of_mul_eq (by rw [Matrix.mul_one, Matrix.one_mul])
        (by rw [hAA1, Matrix.one_mul]) hAne
    obtain ⟨z, hzK, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
    have hAz : A *ᵥ z = z := mem_ker_sub_one_iff.mp hzK
    have hzB : spForm r F z (B *ᵥ z) = 0 := by
      have h1 : spForm r F (A *ᵥ z) (A *ᵥ (B *ᵥ z)) = spForm r F z (B *ᵥ z) :=
        spForm_mulVec_of_isometry hA z (B *ᵥ z)
      have hABz : A *ᵥ (B *ᵥ z) = -(B *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, hAB, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hAz]
      rw [hAz, hABz, map_neg] at h1
      have hneg : spForm r F z (B *ᵥ z) = - spForm r F z (B *ᵥ z) := h1.symm
      have htwo : (2 : F) * spForm r F z (B *ᵥ z) = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp hneg
      exact (mul_eq_zero.mp htwo).resolve_left h2F
    have hS : ∀ x ∈ ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)),
        ∀ y ∈ ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)), spForm r F x y = 0 := by
      intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rw [hx, hy]; exact spForm_isAlt.self_eq_zero z
      · rw [hx, hy]; exact hzB
      · rw [hx, hy, spForm_swap, hzB, neg_zero]
      · rw [hx, hy, spForm_mulVec_of_similitude hB z z,
          spForm_isAlt.self_eq_zero z, mul_zero]
    refine ⟨Submodule.span F ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)), ?_,
      spForm_span_eq_zero hS, ?_, ?_⟩
    · rw [Submodule.ne_bot_iff]
      exact ⟨z, Submodule.subset_span (by simp), hz0⟩
    · refine mulVec_mem_span ?_
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · rw [hAz]
        exact Submodule.subset_span (by simp)
      · rw [Matrix.mulVec_mulVec, hAB, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hAz]
        exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
    · refine mulVec_mem_span ?_
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · rw [Matrix.mulVec_mulVec, hBB, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  ·
    have hAAm : A * A = -1 := by rw [hεm1] at hAA; simpa using hAA
    rcases hβν with hβν | hβν
    ·
      have hBBν : B * B = ν • 1 := by rw [hβν] at hBB; exact hBB
      exact exists_isotropic_of_anticommute_of_eq hF (by omega) hA hAAm hB hν hBBν hAB
    ·
      have hBadj : Bᵀ * formJ r F = -(formJ r F * B) := by
        have h1 : (Bᵀ * formJ r F * B) * B = (Bᵀ * formJ r F) * (B * B) := by
          simp only [Matrix.mul_assoc]
        have h2 : (Bᵀ * formJ r F) * (B * B) = β • (Bᵀ * formJ r F) := by
          rw [hBB, Matrix.mul_smul, Matrix.mul_one]
        have h3 : β • (Bᵀ * formJ r F) = ν • (formJ r F * B) := by
          have h0 := congrArg (fun M => M * B) hB
          rwa [h1, h2, Matrix.smul_mul] at h0
        rw [hβν] at h3
        rw [neg_smul, ← smul_neg] at h3
        have h' := congrArg (fun M => ν⁻¹ • M) h3
        rw [smul_smul, smul_smul, inv_mul_cancel₀ hν0, one_smul, one_smul] at h'
        exact neg_eq_iff_eq_neg.mp h'
      have hneg1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
      obtain ⟨x, y, hxy⟩ := exists_sq_add_sq (F := F) h2F hneg1 hβ0 (-1)
      have hxy' : -x ^ 2 + β * y ^ 2 = 1 := by linear_combination hxy
      let P : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F := x • A + y • B
      have hPdef : P = x • A + y • B := rfl
      have hPP : P * P = 1 := by
        rw [hPdef]
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
        rw [hAAm, hAB, hBB]
        rw [show B * A = -(A * B) from by rw [hAB, neg_neg]]
        linear_combination (norm := module) hxy' •
          (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
      have hBA : B * A = -(A * B) := by rw [hAB, neg_neg]
      have hAC : A * (A * B) = -B := by
        rw [← Matrix.mul_assoc, hAAm, Matrix.neg_mul, Matrix.one_mul]
      have hBC : B * (A * B) = -(β • A) := by
        rw [← Matrix.mul_assoc, hBA, Matrix.neg_mul, Matrix.mul_assoc, hBB,
          Matrix.mul_smul, Matrix.mul_one]
      have hCBA : (A * B) * A = B := by
        rw [Matrix.mul_assoc, hBA, Matrix.mul_neg, ← Matrix.mul_assoc, hAAm,
          Matrix.neg_mul, Matrix.one_mul, neg_neg]
      have hCBB : (A * B) * B = β • A := by
        rw [Matrix.mul_assoc, hBB, Matrix.mul_smul, Matrix.mul_one]
      have hCC : (A * B) * (A * B) = β • 1 := by
        rw [← Matrix.mul_assoc, hCBA, hBB]
      have hPC : P * (A * B) = -(x • B) - (y * β) • A := by
        rw [hPdef, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hAC, hBC,
          smul_neg, smul_neg, ← smul_smul]
        abel
      have hCP : (A * B) * P = -(P * (A * B)) := by
        rw [hPC, hPdef, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hCBA, hCBB,
          smul_smul]
        abel
      have hAP : A = -(x • P) - y • (P * (A * B)) := by
        rw [hPC, hPdef]
        linear_combination (norm := module) (-1 : F) • (hxy' • A)
      have hBP : B = (y * β) • P + x • (P * (A * B)) := by
        rw [hPC, hPdef]
        linear_combination (norm := module) (-1 : F) • (hxy' • B)
      obtain ⟨U, hU, hU3⟩ := exists_eigenspace_finrank_ge (A := P) h2F hPP
      have hU3' : 3 ≤ Module.finrank F U := le_trans hr hU3
      obtain ⟨u, hu, hu0, huCW⟩ :=
        CFSG.FiniteField.exists_mem_ne_zero_dotProduct_mulVec_eq_zero U hU3'
          (formJ r F * (A * B))
      have hCu : spForm r F u ((A * B) *ᵥ u) = 0 := by
        rw [spForm_apply, Matrix.mulVec_mulVec]
        rw [show CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F r = formJ r F from rfl]
        exact huCW
      have hδ : ∃ δ : F, (δ = 1 ∨ δ = -1) ∧ P *ᵥ u = δ • u := by
        rcases hU with hU | hU
        · refine ⟨1, Or.inl rfl, ?_⟩
          rw [hU] at hu
          rw [mem_ker_sub_one_iff] at hu
          simpa using hu
        · refine ⟨-1, Or.inr rfl, ?_⟩
          rw [hU] at hu
          rw [mem_ker_add_one_iff] at hu
          simpa using hu
      obtain ⟨δ, hδ, hPu⟩ := hδ
      have hPCu : P *ᵥ ((A * B) *ᵥ u) = (-δ) • ((A * B) *ᵥ u) := by
        rw [Matrix.mulVec_mulVec,
          show P * (A * B) = -((A * B) * P) from by rw [hCP, neg_neg],
          Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hPu, Matrix.mulVec_smul, ← neg_smul]
      have h33 : spForm r F ((A * B) *ᵥ u) ((A * B) *ᵥ u) = 0 := by
        rw [← Matrix.mulVec_mulVec, spForm_mulVec_of_isometry hA (B *ᵥ u) (B *ᵥ u),
          spForm_mulVec_of_similitude hB u u, spForm_isAlt.self_eq_zero u, mul_zero]
      have hS : ∀ x ∈ ({u, (A * B) *ᵥ u} : Set (Fin r ⊕ Fin r → F)),
          ∀ y ∈ ({u, (A * B) *ᵥ u} : Set (Fin r ⊕ Fin r → F)), spForm r F x y = 0 := by
        intro x hx y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · rw [hx, hy]; exact spForm_isAlt.self_eq_zero u
        · rw [hx, hy]; exact hCu
        · rw [hx, hy, spForm_swap, hCu, neg_zero]
        · rw [hx, hy]; exact h33
      let W : Submodule F (Fin r ⊕ Fin r → F) :=
        Submodule.span F ({u, (A * B) *ᵥ u} : Set (Fin r ⊕ Fin r → F))
      have hWdef : W = Submodule.span F ({u, (A * B) *ᵥ u} : Set (Fin r ⊕ Fin r → F)) := rfl
      have hPgen : ∀ s ∈ ({u, (A * B) *ᵥ u} : Set (Fin r ⊕ Fin r → F)), P *ᵥ s ∈ W := by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with hs | hs
        · rw [hs, hPu, hWdef]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        · rw [hs, hPCu, hWdef]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      have hCgen : ∀ s ∈ ({u, (A * B) *ᵥ u} : Set (Fin r ⊕ Fin r → F)),
          (A * B) *ᵥ s ∈ W := by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with hs | hs
        · rw [hs, hWdef]
          exact Submodule.subset_span (by simp)
        · rw [hs, Matrix.mulVec_mulVec, hCC, Matrix.smul_mulVec, Matrix.one_mulVec, hWdef]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      have hPW : ∀ w ∈ W, P *ᵥ w ∈ W := mulVec_mem_span hPgen
      have hCW : ∀ w ∈ W, (A * B) *ᵥ w ∈ W := mulVec_mem_span hCgen
      have hAW : ∀ w ∈ W, A *ᵥ w ∈ W := by
        intro w hw
        rw [hAP, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
          Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
        exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ (hPW w hw)))
          (Submodule.smul_mem _ _ (hPW _ (hCW w hw)))
      have hBW : ∀ w ∈ W, B *ᵥ w ∈ W := by
        intro w hw
        rw [hBP, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
          ← Matrix.mulVec_mulVec]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hPW w hw))
          (Submodule.smul_mem _ _ (hPW _ (hCW w hw)))
      refine ⟨W, ?_, ?_, hAW, hBW⟩
      · rw [Submodule.ne_bot_iff]
        exact ⟨u, by rw [hWdef]; exact Submodule.subset_span (by simp), hu0⟩
      · rw [hWdef]
        exact spForm_span_eq_zero hS


end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
