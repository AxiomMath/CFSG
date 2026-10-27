module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
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

private lemma transpose_smul_one_mul_formJ (c : F) :
    (c • 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ * formJ r F * (c • 1) =
      (c * c) • formJ r F := by
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul]

private lemma smul_one_mul_self (c : F) :
    (c • 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) * (c • 1) = (c * c) • 1 := by
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]

private lemma smul_formJ_eq (i : Fin r) {c c' : F}
    (h : c • formJ r F = c' • formJ r F) : c = c' := by
  have h' := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  simpa [formJ] using h'

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

private lemma isSquare_mul_of_not_isSquare [Finite F] {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha (by rw [h]; exact IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (by rw [h]; exact IsSquare.zero)
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)]
  rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr ha,
    quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

private lemma beta_eq_or_neg (i : Fin r)
    {B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {ν β : F} (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hBB : B * B = β • 1)
    (hν : ¬ IsSquare ν) : ν ≠ 0 ∧ β ≠ 0 ∧ (β = ν ∨ β = -ν) := by
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact IsSquare.zero)
  have hβ2 : β * β = ν * ν := by
    have h1 : (B * B)ᵀ * formJ r F * (B * B) = (β * β) • formJ r F := by
      rw [hBB, transpose_smul_one_mul_formJ]
    have h2 : (B * B)ᵀ * formJ r F * (B * B) = (ν * ν) • formJ r F := by
      rw [mul_transpose_formJ_mul hB B, hB, smul_smul]
    exact smul_formJ_eq i (h1.symm.trans h2)
  have hβν : β = ν ∨ β = -ν := by
    have hfac : (β - ν) * (β + ν) = 0 := by linear_combination hβ2
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  refine ⟨hν0, ?_, hβν⟩
  rcases hβν with h | h
  · rw [h]; exact hν0
  · rw [h]; exact neg_ne_zero.mpr hν0

private lemma exists_isotropic_of_involution [Finite F]
    {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {ν β : F}
    (h2 : (2 : F) ≠ 0) (hr : 3 ≤ r) (hAA : A * A = 1)
    (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hBB : B * B = β • 1)
    (hAB : A * B = B * A) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  obtain ⟨U, hU, hU3⟩ := exists_eigenspace_finrank_ge (r := r) h2 hAA
  have hU3' : 3 ≤ Module.finrank F ↥U := le_trans hr hU3
  obtain ⟨z, hzU, hz0, hzCW⟩ :=
    CFSG.FiniteField.exists_mem_ne_zero_dotProduct_mulVec_eq_zero U hU3' (formJ r F * B)
  have hzB : spForm r F z (B *ᵥ z) = 0 := by
    rw [spForm_apply, Matrix.mulVec_mulVec]
    rw [show CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F r = formJ r F from rfl]
    exact hzCW
  have hAz : A *ᵥ z = z ∨ A *ᵥ z = -z := by
    rcases hU with hU | hU
    · left
      rw [← mem_ker_sub_one_iff, ← hU]
      exact hzU
    · right
      rw [← mem_ker_add_one_iff, ← hU]
      exact hzU
  have hspan_iso : ∀ x ∈ ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)),
      ∀ y ∈ ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)), spForm r F x y = 0 := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy]; exact spForm_isAlt.self_eq_zero z
    · rw [hx, hy]; exact hzB
    · rw [hx, hy, spForm_swap z (B *ᵥ z), hzB, neg_zero]
    · rw [hx, hy, spForm_mulVec_of_similitude hB z z]
      rw [spForm_isAlt.self_eq_zero z, mul_zero]
  have hAzW : A *ᵥ z ∈ Submodule.span F ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)) := by
    rcases hAz with h | h
    · rw [h]; exact Submodule.subset_span (by simp)
    · rw [h]; exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  have hABzW :
      A *ᵥ (B *ᵥ z) ∈ Submodule.span F ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)) := by
    rw [Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec]
    have hBz : B *ᵥ z ∈ Submodule.span F ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)) :=
      Submodule.subset_span (by simp)
    rcases hAz with h | h
    · rw [h]; exact hBz
    · rw [h, Matrix.mulVec_neg]; exact Submodule.neg_mem _ hBz
  refine ⟨Submodule.span F ({z, B *ᵥ z} : Set (Fin r ⊕ Fin r → F)), ?_,
    spForm_span_eq_zero hspan_iso, ?_, ?_⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨z, Submodule.subset_span (by simp), hz0⟩
  · refine mulVec_mem_span ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hAzW
    · exact hABzW
  · refine mulVec_mem_span ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · rw [Matrix.mulVec_mulVec, hBB, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private lemma exists_isotropic_of_sq_scalar (i : Fin r)
    {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {ν β s : F}
    (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hBB : B * B = β • 1)
    (hs : β = s * s) (hν : ¬ IsSquare ν) (hAB : A * B = B * A) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  have hBsq : B * B = (s * s) • 1 := by rw [hBB, hs]
  have hBne : B ≠ -(s • 1) := by
    intro hBneg
    have h1 : Bᵀ * formJ r F * B = (s * s) • formJ r F := by
      rw [hBneg, ← neg_smul, transpose_smul_one_mul_formJ]
      rw [show (-s) * (-s) = s * s by ring]
    have hsqν : s * s = ν := smul_formJ_eq i (h1.symm.trans hB)
    exact hν ⟨s, hsqν.symm⟩
  have hW0 : LinearMap.ker (Matrix.toLin' (B - s • 1)) ≠ ⊥ :=
    ker_sub_ne_bot_of_mul_eq
      (by rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul])
      (by rw [hBsq, smul_one_mul_self]) hBne
  refine ⟨LinearMap.ker (Matrix.toLin' (B - s • 1)), hW0, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hx' : B *ᵥ x = s • x := by
      have h := mem_ker_sub_iff.mp hx
      rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    have hy' : B *ᵥ y = s • y := by
      have h := mem_ker_sub_iff.mp hy
      rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    have h1 : spForm r F (B *ᵥ x) (B *ᵥ y) = ν * spForm r F x y :=
      spForm_mulVec_of_similitude hB x y
    rw [hx', hy'] at h1
    have h2' : spForm r F (s • x) (s • y) = (s * s) * spForm r F x y := by
      rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, smul_eq_mul]
    rw [h2', ← hs] at h1
    have hβνne : β ≠ ν := fun h => hν ⟨s, by rw [← h]; exact hs⟩
    have hzero : (β - ν) * spForm r F x y = 0 := by rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hβνne)
  · intro w hw
    rw [mem_ker_sub_iff] at hw ⊢
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hw ⊢
    rw [Matrix.mulVec_mulVec, ← hAB, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  · intro w hw
    rw [mem_ker_sub_iff] at hw ⊢
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hw ⊢
    rw [Matrix.mulVec_mulVec, hBsq, Matrix.smul_mulVec, Matrix.one_mulVec, hw, smul_smul]

private lemma exists_isotropic_of_neg_sq_scalar (j : Fin r)
    {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {i : F}
    (h2 : (2 : F) ≠ 0) (hA : Aᵀ * formJ r F * A = formJ r F)
    (hAA : A * A = (-1 : F) • 1) (hi : (-1 : F) = i * i) (hAB : A * B = B * A) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  have hAsq : A * A = (i * i) • 1 := by rw [hAA, ← hi]
  have hAne : A ≠ -(i • 1) := by
    intro hAneg
    have h1 : Aᵀ * formJ r F * A = (i * i) • formJ r F := by
      rw [hAneg, ← neg_smul, transpose_smul_one_mul_formJ]
      rw [show (-i) * (-i) = i * i by ring]
    have hsmul : (i * i) • formJ r F = (1 : F) • formJ r F := by
      rw [one_smul, ← h1, hA]
    have hii : i * i = 1 := smul_formJ_eq j hsmul
    have hneg : (-1 : F) = 1 := hi.trans hii
    have htwo : (2 : F) = 0 := by
      rw [show (2 : F) = 1 - (-1) by ring, hneg, sub_self]
    exact h2 htwo
  have hW0 : LinearMap.ker (Matrix.toLin' (A - i • 1)) ≠ ⊥ :=
    ker_sub_ne_bot_of_mul_eq
      (by rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul])
      (by rw [hAsq, smul_one_mul_self]) hAne
  refine ⟨LinearMap.ker (Matrix.toLin' (A - i • 1)), hW0, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hx' : A *ᵥ x = i • x := by
      have h := mem_ker_sub_iff.mp hx
      rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    have hy' : A *ᵥ y = i • y := by
      have h := mem_ker_sub_iff.mp hy
      rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    have h1 : spForm r F x y = spForm r F (A *ᵥ x) (A *ᵥ y) :=
      (spForm_mulVec_of_isometry hA x y).symm
    rw [hx', hy'] at h1
    have h2' : spForm r F (i • x) (i • y) = (i * i) * spForm r F x y := by
      rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, smul_eq_mul]
    rw [h2', ← hi] at h1
    have hneg : spForm r F x y = - spForm r F x y := h1.trans (neg_one_mul _)
    have htwo : (2 : F) * spForm r F x y = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp hneg
    exact (mul_eq_zero.mp htwo).resolve_left h2
  · intro w hw
    rw [mem_ker_sub_iff] at hw ⊢
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hw ⊢
    have h1 : A *ᵥ (A *ᵥ w) = (-1 : F) • w := by
      rw [Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2' : i • (A *ᵥ w) = (-1 : F) • w := by
      rw [hw, smul_smul, ← hi]
    rw [h1, h2']
  · intro w hw
    rw [mem_ker_sub_iff] at hw ⊢
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hw ⊢
    rw [Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]

private lemma exists_isotropic_of_two_nonsquares [Finite F] (j : Fin r)
    {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {ν β : F}
    (h2 : (2 : F) ≠ 0) (hA : Aᵀ * formJ r F * A = formJ r F)
    (hAA : A * A = (-1 : F) • 1) (hB : Bᵀ * formJ r F * B = ν • formJ r F)
    (hBB : B * B = β • 1) (hAB : A * B = B * A) (hν : ¬ IsSquare ν)
    (hβsq : ¬ IsSquare β) (hm1 : ¬ IsSquare (-1 : F)) (hβ0 : β ≠ 0)
    (hβν : β = ν ∨ β = -ν) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  have hβeq : β = ν := by
    rcases hβν with h | h
    · exact h
    · exfalso
      have hsq : IsSquare β := by
        have h' := isSquare_mul_of_not_isSquare hm1 hν
        rwa [neg_one_mul, ← h] at h'
      exact hβsq hsq
  have hβinv : ¬ IsSquare β⁻¹ := fun h => hβsq (isSquare_inv.mp h)
  obtain ⟨t, ht⟩ := isSquare_mul_of_not_isSquare hm1 hβinv
  have ht' : t * t = -β⁻¹ := by rw [← ht, neg_one_mul]
  set C : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F := t • B with hCdef
  have hAC : A * C = C * A := by
    rw [hCdef, Matrix.mul_smul, Matrix.smul_mul, hAB]
  have hBC : B * C = C * B := by
    rw [hCdef, Matrix.mul_smul, Matrix.smul_mul]
  have hν0 : ν ≠ 0 := by rwa [← hβeq]
  have hCJ : Cᵀ * formJ r F * C = -formJ r F := by
    rw [hCdef]
    calc (t • B)ᵀ * formJ r F * (t • B)
        = (t • Bᵀ) * formJ r F * (t • B) := by rw [Matrix.transpose_smul]
      _ = (t • (Bᵀ * formJ r F)) * (t • B) := by rw [Matrix.smul_mul]
      _ = t • ((Bᵀ * formJ r F) * (t • B)) := by rw [Matrix.smul_mul]
      _ = t • (t • ((Bᵀ * formJ r F) * B)) := by rw [Matrix.mul_smul]
      _ = (t * t) • ((Bᵀ * formJ r F) * B) := by rw [smul_smul]
      _ = (t * t) • (ν • formJ r F) := by rw [hB]
      _ = (t * (t * ν)) • formJ r F := by rw [smul_smul, mul_assoc]
      _ = -formJ r F := by
        have ht2ν : t * (t * ν) = -1 := by
          rw [← mul_assoc, ht', ← hβeq, neg_mul, inv_mul_cancel₀ hβ0]
        rw [ht2ν, neg_one_smul]
  have hCC : C * C = -1 := by
    rw [hCdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBB, smul_smul]
    have ht2β : t * t * β = -1 := by
      rw [ht', neg_mul, inv_mul_cancel₀ hβ0]
    rw [ht2β, neg_one_smul]
  have hAne : A ≠ -C := by
    intro hAneg
    have h1 : Aᵀ * formJ r F * A = -formJ r F := by
      rw [hAneg, Matrix.transpose_neg]
      simpa [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hCJ
    have h2J : (1 : F) • formJ r F = (-1 : F) • formJ r F := by
      rw [one_smul, neg_one_smul]
      exact hA.symm.trans h1
    have h12 : (1 : F) = -1 := smul_formJ_eq j h2J
    have htwo : (2 : F) = 0 := by
      rw [show (2 : F) = 1 - (-1) by ring]
      exact sub_eq_zero.mpr h12
    exact h2 htwo
  have hW0 : LinearMap.ker (Matrix.toLin' (A - C)) ≠ ⊥ :=
    ker_sub_ne_bot_of_mul_eq hAC (by rw [hAA, hCC, neg_one_smul]) hAne
  refine ⟨LinearMap.ker (Matrix.toLin' (A - C)), hW0, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hx' : A *ᵥ x = C *ᵥ x := mem_ker_sub_iff.mp hx
    have hy' : A *ᵥ y = C *ᵥ y := mem_ker_sub_iff.mp hy
    have h1 : spForm r F x y = spForm r F (A *ᵥ x) (A *ᵥ y) :=
      (spForm_mulVec_of_isometry hA x y).symm
    rw [hx', hy'] at h1
    have hC' : Cᵀ * formJ r F * C = (-1 : F) • formJ r F := by
      rw [hCJ, neg_one_smul]
    have h2' : spForm r F (C *ᵥ x) (C *ᵥ y) = - spForm r F x y := by
      rw [spForm_mulVec_of_similitude hC']
      ring
    have hneg : spForm r F x y = - spForm r F x y := h1.trans h2'
    have htwo : (2 : F) * spForm r F x y = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp hneg
    exact (mul_eq_zero.mp htwo).resolve_left h2
  · intro w hw
    rw [mem_ker_sub_iff] at hw ⊢
    have h1 : A *ᵥ (A *ᵥ w) = (-1 : F) • w := by
      rw [Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2' : C *ᵥ (A *ᵥ w) = (-1 : F) • w := by
      rw [hw, Matrix.mulVec_mulVec, hCC, Matrix.neg_mulVec, Matrix.one_mulVec,
        neg_one_smul]
    rw [h1, h2']
  · intro w hw
    rw [mem_ker_sub_iff] at hw ⊢
    have h2' : A *ᵥ (B *ᵥ w) = C *ᵥ (B *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hBC,
        ← Matrix.mulVec_mulVec]
    exact h2'

theorem exists_isotropic_of_commute_of_neg {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) {r : ℕ} (hr : 1 ≤ r) {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {ν β : F} (hA : Aᵀ * formJ r F * A = formJ r F) (hAA : A * A = -1)
    (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hν : ¬ IsSquare ν) (hBB : B * B = β • 1)
    (hAB : A * B = B * A) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hAA' : A * A = (-1 : F) • 1 := by rw [hAA, neg_one_smul]
  let i : Fin r := ⟨0, by omega⟩
  obtain ⟨_, hβ0, hβν⟩ := beta_eq_or_neg (r := r) i hB hBB hν
  by_cases hβsq : IsSquare β
  · obtain ⟨s, hs⟩ := hβsq
    exact exists_isotropic_of_sq_scalar (r := r) i hB hBB hs hν hAB
  · by_cases hm1 : IsSquare (-1 : F)
    · obtain ⟨j, hj⟩ := hm1
      exact exists_isotropic_of_neg_sq_scalar (r := r) i h2 hA hAA' hj hAB
    · exact exists_isotropic_of_two_nonsquares (r := r) i h2 hA hAA' hB hBB hAB hν hβsq hm1
        hβ0 hβν

theorem exists_isotropic_of_commute {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    {r : ℕ} (hr : 3 ≤ r) {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {ε ν β : F}
    (hA : Aᵀ * formJ r F * A = formJ r F) (hAA : A * A = ε • 1) (hε : ε = 1 ∨ ε = -1)
    (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hν : ¬ IsSquare ν) (hBB : B * B = β • 1)
    (hAB : A * B = B * A) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, A *ᵥ w ∈ W) ∧ ∀ w ∈ W, B *ᵥ w ∈ W := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rcases hε with rfl | rfl
  · exact exists_isotropic_of_involution (r := r) h2 hr (by simpa using hAA) hB hBB hAB
  · exact exists_isotropic_of_commute_of_neg (r := r) hF (by omega) hA (by simpa using hAA)
      hB hν hBB hAB

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
