module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SpFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpQv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
  (spForm spT spN spForm_swap spForm_self spN_comm spForm_mulVec conj_spN exists_spForm_sep)

variable {r : ℕ} {K : Type} [Field K]

private lemma spForm_add_right (y z w : Fin r ⊕ Fin r → K) :
    spForm y (z + w) = spForm y z + spForm y w := by
  simp [spForm, Matrix.mulVec_add, dotProduct_add]

private lemma spForm_smul_right (y z : Fin r ⊕ Fin r → K) (c : K) :
    spForm y (c • z) = c * spForm y z := by
  simp [spForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma spForm_neg_left (y z : Fin r ⊕ Fin r → K) :
    spForm (-y) z = -spForm y z := by
  simp [spForm, dotProduct, Finset.sum_neg_distrib]

private lemma spForm_neg_right (y z : Fin r ⊕ Fin r → K) :
    spForm y (-z) = -spForm y z := by
  simp [spForm, Matrix.mulVec_neg, dotProduct_neg]

private lemma spT_smul_left (c a : Fin r ⊕ Fin r → K) (s : K) :
    spT (s • c) a = s • spT c a := by
  simp only [spT, Matrix.mulVec_smul, vecMulVec_smul]

private lemma spT_smul_right (c a : Fin r ⊕ Fin r → K) (s : K) :
    spT c (s • a) = s • spT c a := by
  simp only [spT, smul_vecMulVec]

private lemma spN_smul_right (a c : Fin r ⊕ Fin r → K) (s : K) :
    spN a (s • c) = s • spN a c := by
  rw [spN, spN, spT_smul_left, spT_smul_right, smul_add]

private lemma spN_neg_right (a c : Fin r ⊕ Fin r → K) :
    spN a (-c) = -spN a c := by
  rw [show -c = (-1 : K) • c by simp, spN_smul_right, neg_one_smul]

private lemma mulVec_mulVec_eq {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hd : a * a = d • 1) (y : Fin r ⊕ Fin r → K) : a *ᵥ (a *ᵥ y) = d • y := by
  rw [Matrix.mulVec_mulVec, hd, Matrix.smul_mulVec, Matrix.one_mulVec]

private lemma isSquare_of_eigen {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hd : a * a = d • 1) {y : Fin r ⊕ Fin r → K} (hy : y ≠ 0) (c : K)
    (h : a *ᵥ y = c • y) : IsSquare d := by
  have h1 : d • y = (c * c) • y := by
    rw [← mulVec_mulVec_eq hd y, h, Matrix.mulVec_smul, h, smul_smul]
  have h2 : (d - c * c) • y = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : d - c * c = 0 := (smul_eq_zero.mp h2).resolve_right hy
  exact ⟨c, by rw [← sub_eq_zero]; exact h3⟩

private lemma notMem_span_singleton_of_nonsquare {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    {d : K} (hd : a * a = d • 1) (hdsq : ¬ IsSquare d) {y : Fin r ⊕ Fin r → K}
    (hy : y ≠ 0) : a *ᵥ y ∉ Submodule.span K {y} := by
  intro h
  rw [Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  exact hdsq (isSquare_of_eigen hd hy c hc.symm)

private lemma transpose_formJ_mul_eq {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hA : aᵀ * formJ r K * a = d • formJ r K) (hd : a * a = d • 1) (hd0 : d ≠ 0) :
    aᵀ * formJ r K = formJ r K * a := by
  have h1 : a * (d⁻¹ • a) = 1 := by
    rw [Matrix.mul_smul, hd, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have h2 : aᵀ * formJ r K * (a * (d⁻¹ • a)) = d • (formJ r K * (d⁻¹ • a)) := by
    rw [← Matrix.mul_assoc, hA, Matrix.smul_mul]
  calc aᵀ * formJ r K = aᵀ * formJ r K * 1 := (Matrix.mul_one _).symm
    _ = aᵀ * formJ r K * (a * (d⁻¹ • a)) := by rw [h1]
    _ = d • (formJ r K * (d⁻¹ • a)) := h2
    _ = d • (d⁻¹ • (formJ r K * a)) := by rw [Matrix.mul_smul]
    _ = formJ r K * a := by rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]

private lemma spForm_self_adjoint {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {d : K}
    (hA : aᵀ * formJ r K * a = d • formJ r K) (hd : a * a = d • 1) (hd0 : d ≠ 0)
    (y z : Fin r ⊕ Fin r → K) : spForm (a *ᵥ y) z = spForm y (a *ᵥ z) := by
  have hJA := transpose_formJ_mul_eq hA hd hd0
  simp only [spForm]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJA,
    ← Matrix.mulVec_mulVec]

private lemma span_four_lt_top (hr : 3 ≤ r) (x₁ x₂ x₃ x₄ : Fin r ⊕ Fin r → K) :
    Submodule.span K ({x₁, x₂, x₃, x₄} : Set (Fin r ⊕ Fin r → K)) < ⊤ := by
  classical
  have hle : Set.finrank K ({x₁, x₂, x₃, x₄} : Set (Fin r ⊕ Fin r → K)) ≤ 4 := by
    have h := finrank_span_finset_le_card (R := K)
      ({x₁, x₂, x₃, x₄} : Finset (Fin r ⊕ Fin r → K))
    have hcard : ({x₁, x₂, x₃, x₄} : Finset (Fin r ⊕ Fin r → K)).card ≤ 4 := by
      have h1 := Finset.card_insert_le x₁ ({x₂, x₃, x₄} : Finset (Fin r ⊕ Fin r → K))
      have h2 := Finset.card_insert_le x₂ ({x₃, x₄} : Finset (Fin r ⊕ Fin r → K))
      have h3 := Finset.card_insert_le x₃ ({x₄} : Finset (Fin r ⊕ Fin r → K))
      have h4 : ({x₄} : Finset (Fin r ⊕ Fin r → K)).card ≤ 1 := by simp
      omega
    simpa using le_trans h hcard
  rw [lt_top_iff_ne_top]
  intro htop
  have h2 : Module.finrank K (⊤ : Submodule K (Fin r ⊕ Fin r → K)) ≤ 4 := htop ▸ hle
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h2
  simp only [Fintype.card_sum, Fintype.card_fin] at h2
  omega

private lemma spForm_mulVec_self_eq_zero {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hself : ∀ y z, spForm (a *ᵥ y) z = spForm y (a *ᵥ z)) (h2 : (2 : K) ≠ 0)
    (y : Fin r ⊕ Fin r → K) : spForm (a *ᵥ y) y = 0 := by
  have h3 : spForm (a *ᵥ y) y = -spForm (a *ᵥ y) y := by
    calc spForm (a *ᵥ y) y = spForm y (a *ᵥ y) := hself y y
      _ = -spForm (a *ᵥ y) y := spForm_swap (a *ᵥ y) y
  have h4 : (2 : K) * spForm (a *ᵥ y) y = 0 := by
    rw [two_mul, (eq_neg_iff_add_eq_zero).mp h3]
  exact (mul_eq_zero.mp h4).resolve_left h2

private lemma mem_span_five {V : Type} [AddCommGroup V] [Module K V]
    (v₁ v₂ v₃ v₄ v₅ x : V)
    (h : x ∈ Submodule.span K ({v₁, v₂, v₃, v₄, v₅} : Set V)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : K, x = c₁ • v₁ + c₂ • v₂ + c₃ • v₃ + c₄ • v₄ + c₅ • v₅ := by
  rw [show ({v₁, v₂, v₃, v₄, v₅} : Set V) =
    insert v₁ (insert v₂ (insert v₃ (insert v₄ {v₅}))) by simp] at h
  rw [Submodule.mem_span_insert] at h
  obtain ⟨c₁, z, hz, rfl⟩ := h
  rw [Submodule.mem_span_insert] at hz
  obtain ⟨c₂, z, hz, rfl⟩ := hz
  rw [Submodule.mem_span_insert] at hz
  obtain ⟨c₃, z, hz, rfl⟩ := hz
  rw [Submodule.mem_span_insert] at hz
  obtain ⟨c₄, z, hz, rfl⟩ := hz
  rw [Submodule.mem_span_singleton] at hz
  obtain ⟨c₅, rfl⟩ := hz
  exact ⟨c₁, c₂, c₃, c₄, c₅, by rw [add_assoc, add_assoc, add_assoc]⟩

theorem exists_frame_inv_ext (hr : 3 ≤ r) (h2 : (2 : K) ≠ 0) (A : GL (Fin r ⊕ Fin r) K) {d : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = d • formJ r K)
    (hd : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A = d • 1) (hdsq : ¬ IsSquare d) :
    ∃ e f : Fin 4 → Fin r ⊕ Fin r → K, IsSpFrame e f ∧
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * frameN e f *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          -frameN e f := by
  classical
  let a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have haA : aᵀ * formJ r K * a = d • formJ r K := hA
  have had : a * a = d • 1 := hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hdsq ⟨0, by simp⟩
  have hself : ∀ y z, spForm (a *ᵥ y) z = spForm y (a *ᵥ z) :=
    spForm_self_adjoint haA had hd0
  have himg : ∀ y, spForm (a *ᵥ y) y = 0 := spForm_mulVec_self_eq_zero hself h2
  obtain ⟨e0, he0⟩ : ∃ e0 : Fin r ⊕ Fin r → K, e0 ≠ 0 := by
    refine ⟨Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K), ?_⟩
    intro h
    have h1 := congrFun h (Sum.inl ⟨0, by omega⟩)
    simp at h1
  have he0span : a *ᵥ e0 ∉ Submodule.span K ({e0} : Set (Fin r ⊕ Fin r → K)) :=
    notMem_span_singleton_of_nonsquare had hdsq he0
  obtain ⟨e1, he1orth, he1val⟩ :=
    exists_spForm_sep (S := {e0}) (c := a *ᵥ e0) he0span
  have he0e1 : spForm e0 e1 = 0 := he1orth e0 (by simp)
  have he1e0 : spForm e1 e0 = 0 := by rw [spForm_swap e0 e1, he0e1, neg_zero]
  have he0ae1 : spForm e0 (a *ᵥ e1) = 1 := by
    rw [← hself e0 e1]
    exact he1val
  have he1ae0 : spForm e1 (a *ᵥ e0) = -1 := by
    rw [← hself e1 e0, spForm_swap e0 (a *ᵥ e1), he0ae1]
  have hae10 : spForm (a *ᵥ e1) e0 = -1 := by
    rw [hself e1 e0]
    exact he1ae0
  have h4lt : Submodule.span K
      ({e0, e1, a *ᵥ e0, a *ᵥ e1} : Set (Fin r ⊕ Fin r → K)) < ⊤ :=
    span_four_lt_top hr e0 e1 (a *ᵥ e0) (a *ᵥ e1)
  obtain ⟨c2, -, hc2⟩ := (SetLike.lt_iff_le_and_exists.mp h4lt).2
  obtain ⟨e2, he2orth, he2val⟩ :=
    exists_spForm_sep (S := {e0, e1, a *ᵥ e0, a *ᵥ e1}) (c := c2) hc2
  have he2ne : e2 ≠ 0 := by
    intro h0
    rw [h0] at he2val
    simp [spForm] at he2val
  have he0e2 : spForm e0 e2 = 0 := he2orth e0 (by simp)
  have he1e2 : spForm e1 e2 = 0 := he2orth e1 (by simp)
  have hae0e2 : spForm (a *ᵥ e0) e2 = 0 := he2orth (a *ᵥ e0) (by simp)
  have hae1e2 : spForm (a *ᵥ e1) e2 = 0 := he2orth (a *ᵥ e1) (by simp)
  have he2e0 : spForm e2 e0 = 0 := by rw [spForm_swap e0 e2, he0e2, neg_zero]
  have he2e1 : spForm e2 e1 = 0 := by rw [spForm_swap e1 e2, he1e2, neg_zero]
  have he0ae0 : spForm e0 (a *ᵥ e0) = 0 := by rw [← hself e0 e0, himg e0]
  have he1ae1 : spForm e1 (a *ᵥ e1) = 0 := by rw [← hself e1 e1, himg e1]
  have he2ae2 : spForm e2 (a *ᵥ e2) = 0 := by
    rw [spForm_swap (a *ᵥ e2) e2, himg e2, neg_zero]
  have he0ae2 : spForm e0 (a *ᵥ e2) = 0 := by rw [← hself e0 e2, hae0e2]
  have he1ae2 : spForm e1 (a *ᵥ e2) = 0 := by rw [← hself e1 e2, hae1e2]
  have he2ae0 : spForm e2 (a *ᵥ e0) = 0 := by
    rw [← hself e2 e0, spForm_swap e0 (a *ᵥ e2), he0ae2, neg_zero]
  have he2ae1 : spForm e2 (a *ᵥ e1) = 0 := by
    rw [← hself e2 e1, spForm_swap e1 (a *ᵥ e2), he1ae2, neg_zero]
  have hae0ae1 : spForm (a *ᵥ e0) (a *ᵥ e1) = 0 := by
    rw [spForm_mulVec haA, he0e1, mul_zero]
  have hae1ae0 : spForm (a *ᵥ e1) (a *ᵥ e0) = 0 := by
    rw [spForm_mulVec haA, spForm_swap e0 e1, he0e1]
    simp
  have hae0ae2 : spForm (a *ᵥ e0) (a *ᵥ e2) = 0 := by
    rw [spForm_mulVec haA, he0e2, mul_zero]
  have hae1ae2 : spForm (a *ᵥ e1) (a *ᵥ e2) = 0 := by
    rw [spForm_mulVec haA, he1e2, mul_zero]
  have hnotmem : a *ᵥ e2 ∉
      Submodule.span K ({e0, e1, a *ᵥ e0, a *ᵥ e1, e2} :
        Set (Fin r ⊕ Fin r → K)) := by
    intro hin
    obtain ⟨α, β, γ, δ, lam, hdec⟩ :=
      mem_span_five e0 e1 (a *ᵥ e0) (a *ᵥ e1) e2 (a *ᵥ e2) hin
    have hβ : β = 0 := by
      have h := congrArg (spForm (a *ᵥ e0)) hdec
      simpa [spForm_add_right, spForm_smul_right, himg, he1val, spForm_self, hae0ae1,
        hae0e2, hae0ae2] using h.symm
    have hα : α = 0 := by
      have h := congrArg (spForm (a *ᵥ e1)) hdec
      simpa [spForm_add_right, spForm_smul_right, hae10, himg, hae1ae0, spForm_self,
        hae1e2, hae1ae2] using h.symm
    have hγ : γ = 0 := by
      have h := congrArg (spForm e1) hdec
      simpa [spForm_add_right, spForm_smul_right, he1e0, spForm_self, he1ae0, he1ae1,
        he1e2, he1ae2] using h.symm
    have hδ : δ = 0 := by
      have h := congrArg (spForm e0) hdec
      simpa [spForm_add_right, spForm_smul_right, spForm_self, he0e1, he0ae0, he0ae1,
        he0e2, he0ae2] using h.symm
    have hlam : a *ᵥ e2 = lam • e2 := by
      rw [hdec, hα, hβ, hγ, hδ]
      simp
    exact hdsq (isSquare_of_eigen had he2ne lam hlam)
  obtain ⟨e3, he3orth, he3val⟩ :=
    exists_spForm_sep (S := {e0, e1, a *ᵥ e0, a *ᵥ e1, e2}) (c := a *ᵥ e2) hnotmem
  have he0e3 : spForm e0 e3 = 0 := he3orth e0 (by simp)
  have he1e3 : spForm e1 e3 = 0 := he3orth e1 (by simp)
  have he2e3 : spForm e2 e3 = 0 := he3orth e2 (by simp)
  have he0ae3 : spForm e0 (a *ᵥ e3) = 0 := by
    rw [← hself e0 e3]
    exact he3orth (a *ᵥ e0) (by simp)
  have he1ae3 : spForm e1 (a *ᵥ e3) = 0 := by
    rw [← hself e1 e3]
    exact he3orth (a *ᵥ e1) (by simp)
  have he2ae3 : spForm e2 (a *ᵥ e3) = 1 := by
    rw [← hself e2 e3]
    exact he3val
  have he3ae2 : spForm e3 (a *ᵥ e2) = -1 := by
    rw [spForm_swap (a *ᵥ e2) e3, he3val]
  have he3ae0 : spForm e3 (a *ᵥ e0) = 0 := by
    rw [← hself e3 e0, spForm_swap e0 (a *ᵥ e3), he0ae3, neg_zero]
  have he3ae1 : spForm e3 (a *ᵥ e1) = 0 := by
    rw [← hself e3 e1, spForm_swap e1 (a *ᵥ e3), he1ae3, neg_zero]
  have he3ae3 : spForm e3 (a *ᵥ e3) = 0 := by rw [← hself e3 e3, himg e3]
  have he3e0 : spForm e3 e0 = 0 := by rw [spForm_swap e0 e3, he0e3, neg_zero]
  have he3e1 : spForm e3 e1 = 0 := by rw [spForm_swap e1 e3, he1e3, neg_zero]
  have he3e2 : spForm e3 e2 = 0 := by rw [spForm_swap e2 e3, he2e3, neg_zero]
  let e : Fin 4 → Fin r ⊕ Fin r → K := ![e0, e1, e2, e3]
  let f : Fin 4 → Fin r ⊕ Fin r → K :=
    ![a *ᵥ e1, -(a *ᵥ e0), a *ᵥ e3, -(a *ᵥ e2)]
  have hee : ∀ i j, spForm (e i) (e j) = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e, spForm_self, he0e1, he0e2, he0e3, he1e0, he1e2, he1e3, he2e0, he2e1,
        he2e3, he3e0, he3e1, he3e2]
  have hff : ∀ i j, spForm (f i) (f j) = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, spForm_neg_left, spForm_neg_right, spForm_mulVec haA, spForm_self,
        he0e1, he0e2, he0e3, he1e0, he1e2, he1e3, he2e0, he2e1, he2e3, he3e0, he3e1,
        he3e2]
  have hef : ∀ i j, spForm (e i) (f j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e, f, spForm_neg_right, he0ae0, he0ae1, he0ae2, he0ae3, he1ae0, he1ae1,
        he1ae2, he1ae3, he2ae0, he2ae1, he2ae2, he2ae3, he3ae0, he3ae1, he3ae2, he3ae3]
  have hframe : IsSpFrame e f := fun i j => ⟨hee i j, hff i j, hef i j⟩
  have hframeN : frameN e f = spN e0 (-(a *ᵥ e2)) - spN e2 (-(a *ᵥ e0)) := by
    simp [frameN, e, f]
  have hconj1 : a * spN e0 (-(a *ᵥ e2)) *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      -spN (a *ᵥ e0) e2 := by
    rw [conj_spN A haA, Matrix.mulVec_neg, mulVec_mulVec_eq had e2, spN_neg_right,
      spN_smul_right, smul_neg, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hconj2 : a * spN e2 (-(a *ᵥ e0)) *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      -spN (a *ᵥ e2) e0 := by
    rw [conj_spN A haA, Matrix.mulVec_neg, mulVec_mulVec_eq had e0, spN_neg_right,
      spN_smul_right, smul_neg, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hmain : a * (spN e0 (-(a *ᵥ e2)) - spN e2 (-(a *ᵥ e0))) *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      -spN (a *ᵥ e0) e2 + spN (a *ᵥ e2) e0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hconj1, hconj2]
    abel
  refine ⟨e, f, hframe, ?_⟩
  change a * frameN e f *
    ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
    -frameN e f
  rw [hframeN, hmain, spN_neg_right, spN_neg_right, spN_comm e0 (a *ᵥ e2),
    spN_comm e2 (a *ᵥ e0)]
  abel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
