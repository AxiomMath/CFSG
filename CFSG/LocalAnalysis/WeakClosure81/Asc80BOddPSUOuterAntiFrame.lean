module

public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

structure AntiFrame (σ : K ≃+* K) (A A' : Matrix (Fin 4) (Fin 4) K) (l : K)
    (f₁ f₂ g₁ g₂ : Fin 4 → K) : Prop where
  af₁ : A *ᵥ f₁ = l • f₁
  af₂ : A *ᵥ f₂ = l • f₂
  ag₁ : A *ᵥ g₁ = (-l) • g₁
  ag₂ : A *ᵥ g₂ = (-l) • g₂
  bf₁ : A' *ᵥ f₁ = l • f₁
  bf₂ : A' *ᵥ f₂ = (-l) • f₂
  bg₁ : A' *ᵥ g₁ = (-l) • g₁
  bg₂ : A' *ᵥ g₂ = l • g₂
  f₁g₁ : herm σ f₁ g₁ = 1
  f₂g₂ : herm σ f₂ g₂ = 1
  f₁f₁ : herm σ f₁ f₁ = 0
  f₂f₂ : herm σ f₂ f₂ = 0
  g₁g₁ : herm σ g₁ g₁ = 0
  g₂g₂ : herm σ g₂ g₂ = 0
  f₁f₂ : herm σ f₁ f₂ = 0
  f₁g₂ : herm σ f₁ g₂ = 0
  f₂g₁ : herm σ f₂ g₁ = 0
  g₁g₂ : herm σ g₁ g₂ = 0
  span : ∀ v : Fin 4 → K, ∃ a b c d : K, v = a • f₁ + b • f₂ + c • g₁ + d • g₂

section EichlerAux

private theorem herm_adjoint_mulVec {n : ℕ} (hσ : ∀ c, σ (σ c) = c)
    (A : Matrix (Fin n) (Fin n) K) (e x : Fin n → K) :
    herm σ e (A *ᵥ x) = herm σ ((A.map σ)ᵀ *ᵥ e) x := by
  have e1 : herm σ e (A *ᵥ x) = (fun i => σ (e i)) ⬝ᵥ (A *ᵥ x) := rfl
  have e2 : herm σ ((A.map σ)ᵀ *ᵥ e) x =
      (fun j => σ (((A.map σ)ᵀ *ᵥ e) j)) ⬝ᵥ x := rfl
  rw [e1, e2, dotProduct_mulVec]
  congr 1
  funext j
  simp only [vecMul, dotProduct, mulVec, Matrix.transpose_apply, Matrix.map_apply, map_sum,
    map_mul, hσ]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem adjoint_mulVec_eigen {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (hAu : (A.map σ)ᵀ * A = 1) {e : Fin n → K} {ε : K} (he : A *ᵥ e = ε • e)
    (hε0 : ε ≠ 0) : (A.map σ)ᵀ *ᵥ e = ε⁻¹ • e := by
  have h1 : ((A.map σ)ᵀ * A) *ᵥ e = e := by rw [hAu, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul] at h1
  have h2 := congrArg (fun w => ε⁻¹ • w) h1
  simpa [smul_smul, inv_mul_cancel₀ hε0] using h2

private theorem sigma_inv_of_norm_neg_one {ε : K} (hε : σ ε * ε = -1) :
    σ ε⁻¹ = -ε := by
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hε
    exact one_ne_zero (neg_eq_zero.1 hε.symm)
  have h : σ ε = -ε⁻¹ := by
    have h1 := congrArg (fun c => c * ε⁻¹) hε
    rw [mul_assoc, mul_inv_cancel₀ hε0, mul_one, neg_mul, one_mul] at h1
    exact h1
  rw [map_inv₀, h, inv_neg, inv_inv]

private theorem herm_eigen_apply {n : ℕ} (hσ : ∀ c, σ (σ c) = c)
    {A : Matrix (Fin n) (Fin n) K} (hAu : (A.map σ)ᵀ * A = 1) {e : Fin n → K} {ε : K}
    (he : A *ᵥ e = ε • e) (hε0 : ε ≠ 0) (x : Fin n → K) :
    herm σ e (A *ᵥ x) = σ ε⁻¹ * herm σ e x := by
  rw [herm_adjoint_mulVec hσ, adjoint_mulVec_eigen hAu he hε0, herm_smul_left]

private theorem herm_eigen_apply_neg {n : ℕ} (hσ : ∀ c, σ (σ c) = c)
    {A : Matrix (Fin n) (Fin n) K} (hAu : (A.map σ)ᵀ * A = 1) {y : Fin n → K} {ε : K}
    (hy : A *ᵥ y = (-ε) • y) (hε0 : ε ≠ 0) (x : Fin n → K) :
    herm σ y (A *ᵥ x) = σ (-ε)⁻¹ * herm σ y x := by
  have h0 : (-ε) ≠ 0 := neg_ne_zero.2 hε0
  rw [herm_adjoint_mulVec hσ, adjoint_mulVec_eigen hAu hy h0, herm_smul_left]

end EichlerAux

theorem eichlerMat_comm_of_eigen (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {l ε : K} (hl : σ l * l = -1) (hε : ε = l ∨ ε = -l)
    (hAu : (A.map σ)ᵀ * A = 1) {e y : Fin n → K} (hee : herm σ e e = 0)
    (he : A *ᵥ e = ε • e) (hy : A *ᵥ y = (-ε) • y) :
    A * eichlerMat σ e y 0 = eichlerMat σ e y 0 * A := by
  have hεnorm : σ ε * ε = -1 := by
    rcases hε with rfl | rfl
    · exact hl
    · rw [map_neg, neg_mul, mul_neg, neg_neg]; exact hl
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hεnorm
    exact one_ne_zero (neg_eq_zero.1 hεnorm.symm)
  have hσinv : σ ε⁻¹ = -ε := sigma_inv_of_norm_neg_one hεnorm
  have hσinv' : σ (-ε)⁻¹ = ε := by
    rw [show (-ε)⁻¹ = -ε⁻¹ by rw [inv_neg], map_neg, hσinv, neg_neg]
  apply Matrix.ext_iff_mulVec.2
  intro x
  have hE : eichlerMat σ e y 0 *ᵥ x = x + herm σ e x • y - herm σ y x • e := by
    simpa using eichlerMat_mulVec (σ := σ) (n := n) hee 0 x
  have hEx : eichlerMat σ e y 0 *ᵥ (A *ᵥ x) =
      A *ᵥ x + herm σ e (A *ᵥ x) • y - herm σ y (A *ᵥ x) • e := by
    simpa using eichlerMat_mulVec (σ := σ) (n := n) hee 0 (A *ᵥ x)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hE, hEx,
    herm_eigen_apply hσ hAu he hε0, herm_eigen_apply_neg hσ hAu hy hε0, hσinv, hσinv']
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, he, hy, smul_smul]
  module

section FrameAux

private def uSgn (s : Bool) : K := if s then 1 else -1

private theorem uSgn_mul_self (s : Bool) : uSgn (K := K) s * uSgn s = 1 := by
  cases s <;> simp [uSgn]

private theorem uSgn_sq (s : Bool) : uSgn (K := K) s ^ 2 = 1 := by
  rw [pow_two, uSgn_mul_self]

private theorem map_uSgn (s : Bool) : σ (uSgn (K := K) s) = uSgn s := by
  cases s <;> simp [uSgn]

private def negSgn (χ : Bool × Bool) : Bool × Bool := (!χ.1, !χ.2)

private theorem negSgn_invol (χ : Bool × Bool) : negSgn (negSgn χ) = χ := by
  rcases χ with ⟨b1, b2⟩
  simp [negSgn]

private def eigM (A : Matrix (Fin 4) (Fin 4) K) (lam : K) : Submodule K (Fin 4 → K) :=
  LinearMap.ker ((A - lam • 1).mulVecLin)

private theorem mem_eigM {A : Matrix (Fin 4) (Fin 4) K} {lam : K} {v : Fin 4 → K} :
    v ∈ eigM A lam ↔ A *ᵥ v = lam • v := by
  simp [eigM, sub_eq_zero]

private theorem herm_eigM_self {A : Matrix (Fin 4) (Fin 4) K}
    (hAiso : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y)
    (h2K : (2 : K) ≠ 0) {lam : K} (hlam : σ lam * lam = -1)
    {x y : Fin 4 → K} (hx : x ∈ eigM A lam) (hy : y ∈ eigM A lam) :
    herm σ x y = 0 := by
  have h := hAiso x y
  rw [mem_eigM.1 hx, mem_eigM.1 hy, herm_smul_left, herm_smul_right] at h
  have h2 : (2 : K) * herm σ x y = 0 := by linear_combination -h + herm σ x y * hlam
  exact (mul_eq_zero.1 h2).resolve_left h2K

private theorem isometry_of_adjoint {A : Matrix (Fin 4) (Fin 4) K}
    (hAu : (A.map σ)ᵀ * A = 1) :
    ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y := by
  intro x y
  rw [herm_mulVec]
  rw [show conjTr σ A = (A.map σ)ᵀ from rfl, hAu, Matrix.one_mulVec]

private theorem norm_uSgn_mul {l : K} (hl : σ l * l = -1) (s : Bool) :
    σ (uSgn s * l) * (uSgn s * l) = -1 := by
  rw [map_mul, map_uSgn]
  calc (uSgn s * σ l) * (uSgn s * l) = (uSgn s * uSgn s) * (σ l * l) := by ring
    _ = -1 := by rw [uSgn_mul_self, hl, one_mul]

private def commEigM (A A' : Matrix (Fin 4) (Fin 4) K) (l : K) (χ : Bool × Bool) :
    Submodule K (Fin 4 → K) :=
  eigM A (uSgn χ.1 * l) ⊓ eigM A' (uSgn χ.2 * l)

private def commProjM (A A' : Matrix (Fin 4) (Fin 4) K) (l : K) (χ : Bool × Bool)
    (v : Fin 4 → K) : Fin 4 → K :=
  (4⁻¹ : K) • (v + (uSgn χ.1 * l⁻¹) • (A *ᵥ v) + (uSgn χ.2 * l⁻¹) • (A' *ᵥ v) +
    (uSgn χ.1 * uSgn χ.2 * l⁻¹ * l⁻¹) • (A *ᵥ (A' *ᵥ v)))

private theorem commProjM_mem {A A' : Matrix (Fin 4) (Fin 4) K} {l : K}
    (hA2 : A * A = (l * l) • 1) (hA'2 : A' * A' = (l * l) • 1)
    (hcomm : A * A' = A' * A) (hl : l ≠ 0) (χ : Bool × Bool) (v : Fin 4 → K) :
    commProjM A A' l χ v ∈ commEigM A A' l χ := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_eigM, commProjM]
    have hAAA : A * (A' * A) = (l * l) • A' := by
      rw [← mul_assoc, hcomm, mul_assoc, hA2]
      simp
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hA2, hcomm, hAAA,
      smul_add, smul_smul]
    match_scalars <;> field_simp [hl] <;> simp [uSgn_sq]
  · rw [mem_eigM, commProjM]
    have hA'A'A : A' * (A' * A) = (l * l) • A := by
      rw [← mul_assoc, hA'2]
      simp
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hA'2, hcomm, hA'A'A,
      smul_add, smul_smul]
    match_scalars <;> field_simp [hl] <;> simp [uSgn_sq]

private theorem sum_commProjM {A A' : Matrix (Fin 4) (Fin 4) K} {l : K}
    (h2K : (2 : K) ≠ 0) (v : Fin 4 → K) :
    ∑ χ : Bool × Bool, commProjM A A' l χ v = v := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2K h2K
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, commProjM, uSgn]
  generalize A *ᵥ v = y₁
  generalize A' *ᵥ v = y₂
  generalize A *ᵥ y₂ = y₃
  simp only [if_true, Bool.false_eq_true, if_false]
  match_scalars <;> field_simp <;> ring

private theorem mulVec_finset_sum {ι : Type} [Fintype ι]
    (M : Matrix (Fin 4) (Fin 4) K) (f : ι → Fin 4 → K) :
    M *ᵥ (∑ i, f i) = ∑ i, M *ᵥ f i := by
  simpa only [Matrix.mulVecLin_apply] using map_sum (Matrix.mulVecLin M) f Finset.univ

private theorem herm_finset_sum {ι : Type} [Fintype ι]
    (x : Fin 4 → K) (f : ι → Fin 4 → K) :
    herm σ x (∑ i, f i) = ∑ i, herm σ x (f i) := by
  simpa only [hermL_apply] using map_sum (hermL σ x) f Finset.univ

private theorem snd_eq_of_ne_negSgn {χ ψ : Bool × Bool} (h : ψ ≠ negSgn χ)
    (h1 : χ.1 ≠ ψ.1) : χ.2 = ψ.2 := by
  revert h h1
  rcases χ with ⟨b1, b2⟩
  rcases ψ with ⟨c1, c2⟩
  cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> simp_all [negSgn]

private theorem herm_commEigM_eq_zero {A A' : Matrix (Fin 4) (Fin 4) K}
    (hAiso : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y)
    (hA'iso : ∀ x y, herm σ (A' *ᵥ x) (A' *ᵥ y) = herm σ x y)
    (h2K : (2 : K) ≠ 0) {l : K} (hl : σ l * l = -1)
    {χ ψ : Bool × Bool} (h : ψ ≠ negSgn χ) {u w : Fin 4 → K}
    (hu : u ∈ commEigM A A' l χ) (hw : w ∈ commEigM A A' l ψ) : herm σ u w = 0 := by
  rcases χ with ⟨χ1, χ2⟩
  rcases ψ with ⟨ψ1, ψ2⟩
  by_cases h1 : χ1 = ψ1
  · have hu' : u ∈ eigM A (uSgn χ1 * l) := (Submodule.mem_inf.1 hu).1
    have hw' : w ∈ eigM A (uSgn ψ1 * l) := (Submodule.mem_inf.1 hw).1
    rw [← h1] at hw'
    exact herm_eigM_self hAiso h2K (norm_uSgn_mul hl χ1) hu' hw'
  · have h2 : χ2 = ψ2 := snd_eq_of_ne_negSgn h h1
    have hu' : u ∈ eigM A' (uSgn χ2 * l) := (Submodule.mem_inf.1 hu).2
    have hw' : w ∈ eigM A' (uSgn ψ2 * l) := (Submodule.mem_inf.1 hw).2
    rw [← h2] at hw'
    exact herm_eigM_self hA'iso h2K (norm_uSgn_mul hl χ2) hu' hw'

private theorem exists_pair_sgn {A A' : Matrix (Fin 4) (Fin 4) K}
    (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0) {l : K}
    (hA2 : A * A = (l * l) • 1) (hA'2 : A' * A' = (l * l) • 1)
    (hcomm : A * A' = A' * A) (hl : σ l * l = -1)
    (hAiso : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y)
    (hA'iso : ∀ x y, herm σ (A' *ᵥ x) (A' *ᵥ y) = herm σ x y)
    (χ : Bool × Bool)
    (h : commEigM A A' l χ ≠ ⊥ ∨ commEigM A A' l (negSgn χ) ≠ ⊥) :
    ∃ f g : Fin 4 → K, f ∈ commEigM A A' l χ ∧ g ∈ commEigM A A' l (negSgn χ) ∧
      herm σ f g = 1 := by
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hl
    exact one_ne_zero (neg_eq_zero.1 hl.symm)
  rcases h with h1 | h2
  · obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h1
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hx0
    have hproj : commProjM A A' l (negSgn χ) y ∈ commEigM A A' l (negSgn χ) :=
      commProjM_mem hA2 hA'2 hcomm hl0 (negSgn χ) y
    have hxy : herm σ x (commProjM A A' l (negSgn χ) y) = herm σ x y := by
      have hsum : (∑ ψ : Bool × Bool, commProjM A A' l ψ y) = y := sum_commProjM h2K y
      have hxs : herm σ x (∑ ψ : Bool × Bool, commProjM A A' l ψ y) = herm σ x y := by
        rw [hsum]
      rw [herm_finset_sum] at hxs
      rw [Finset.sum_eq_single (negSgn χ)] at hxs
      · exact hxs
      · intro ψ _ hψ
        exact herm_commEigM_eq_zero hAiso hA'iso h2K hl hψ hx
          (commProjM_mem hA2 hA'2 hcomm hl0 ψ y)
      · intro hnot
        exact absurd (Finset.mem_univ (negSgn χ)) hnot
    have hne0 : herm σ x (commProjM A A' l (negSgn χ) y) ≠ 0 := by
      rw [hxy]
      exact hy
    exact ⟨x, (herm σ x (commProjM A A' l (negSgn χ) y))⁻¹ •
        commProjM A A' l (negSgn χ) y, hx, Submodule.smul_mem _ _ hproj,
      by rw [herm_smul_right, inv_mul_cancel₀ hne0]⟩
  · obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hx0
    have hproj : commProjM A A' l χ y ∈ commEigM A A' l χ :=
      commProjM_mem hA2 hA'2 hcomm hl0 χ y
    have hxf : herm σ x (commProjM A A' l χ y) = herm σ x y := by
      have hsum : (∑ ψ : Bool × Bool, commProjM A A' l ψ y) = y := sum_commProjM h2K y
      have hxs : herm σ x (∑ ψ : Bool × Bool, commProjM A A' l ψ y) = herm σ x y := by
        rw [hsum]
      rw [herm_finset_sum] at hxs
      rw [Finset.sum_eq_single χ] at hxs
      · exact hxs
      · intro ψ _ hψ
        exact herm_commEigM_eq_zero hAiso hA'iso h2K hl
          (by rwa [negSgn_invol] : ψ ≠ negSgn (negSgn χ)) hx
          (commProjM_mem hA2 hA'2 hcomm hl0 ψ y)
      · intro hnot
        exact absurd (Finset.mem_univ χ) hnot
    have hH : herm σ (commProjM A A' l χ y) x ≠ 0 := by
      intro hzero
      have h1 : herm σ x (commProjM A A' l χ y) = 0 := by
        have hconj := congrArg σ hzero
        rwa [herm_conj σ hσ.invol x (commProjM A A' l χ y), hσ.invol, map_zero] at hconj
      rw [hxf] at h1
      exact hy h1
    exact ⟨commProjM A A' l χ y, (herm σ (commProjM A A' l χ y) x)⁻¹ • x, hproj,
      Submodule.smul_mem _ _ hx, by rw [herm_smul_right, inv_mul_cancel₀ hH]⟩

private theorem eq_neg_of_bot_pp_mm {A A' : Matrix (Fin 4) (Fin 4) K} {l : K}
    (h2K : (2 : K) ≠ 0) (hA2 : A * A = (l * l) • 1)
    (hA'2 : A' * A' = (l * l) • 1) (hcomm : A * A' = A' * A) (hl : σ l * l = -1)
    (h1 : commEigM A A' l (true, true) = ⊥)
    (h2 : commEigM A A' l (false, false) = ⊥) : A' = -A := by
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hl
    exact one_ne_zero (neg_eq_zero.1 hl.symm)
  apply Matrix.ext_iff_mulVec.2
  intro v
  have hv : v = ∑ χ : Bool × Bool, commProjM A A' l χ v := (sum_commProjM h2K v).symm
  calc A' *ᵥ v = ∑ χ : Bool × Bool, A' *ᵥ commProjM A A' l χ v := by
        conv_lhs => rw [hv]
        exact mulVec_finset_sum A' _
    _ = ∑ χ : Bool × Bool, (-A) *ᵥ commProjM A A' l χ v := by
        refine Finset.sum_congr rfl ?_
        intro χ _
        rcases χ with ⟨b1, b2⟩
        cases b1 <;> cases b2
        · have hp : commProjM A A' l (false, false) v = 0 := by
            have hmem := commProjM_mem hA2 hA'2 hcomm hl0 (false, false) v
            rw [h2] at hmem
            simpa using hmem
          simp [hp]
        · have hp := commProjM_mem hA2 hA'2 hcomm hl0 (false, true) v
          have hAP : A *ᵥ commProjM A A' l (false, true) v =
              (-l) • commProjM A A' l (false, true) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).1
          have hA'P : A' *ᵥ commProjM A A' l (false, true) v =
              l • commProjM A A' l (false, true) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).2
          rw [hA'P, Matrix.neg_mulVec, hAP]
          simp
        · have hp := commProjM_mem hA2 hA'2 hcomm hl0 (true, false) v
          have hAP : A *ᵥ commProjM A A' l (true, false) v =
              l • commProjM A A' l (true, false) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).1
          have hA'P : A' *ᵥ commProjM A A' l (true, false) v =
              (-l) • commProjM A A' l (true, false) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).2
          rw [hA'P, Matrix.neg_mulVec, hAP]
          simp
        · have hp : commProjM A A' l (true, true) v = 0 := by
            have hmem := commProjM_mem hA2 hA'2 hcomm hl0 (true, true) v
            rw [h1] at hmem
            simpa using hmem
          simp [hp]
    _ = (-A) *ᵥ (∑ χ : Bool × Bool, commProjM A A' l χ v) :=
        (mulVec_finset_sum (-A) _).symm
    _ = (-A) *ᵥ v := by rw [sum_commProjM h2K v]

private theorem eq_self_of_bot_pm_mp {A A' : Matrix (Fin 4) (Fin 4) K} {l : K}
    (h2K : (2 : K) ≠ 0) (hA2 : A * A = (l * l) • 1)
    (hA'2 : A' * A' = (l * l) • 1) (hcomm : A * A' = A' * A) (hl : σ l * l = -1)
    (h1 : commEigM A A' l (true, false) = ⊥)
    (h2 : commEigM A A' l (false, true) = ⊥) : A' = A := by
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hl
    exact one_ne_zero (neg_eq_zero.1 hl.symm)
  apply Matrix.ext_iff_mulVec.2
  intro v
  have hv : v = ∑ χ : Bool × Bool, commProjM A A' l χ v := (sum_commProjM h2K v).symm
  calc A' *ᵥ v = ∑ χ : Bool × Bool, A' *ᵥ commProjM A A' l χ v := by
        conv_lhs => rw [hv]
        exact mulVec_finset_sum A' _
    _ = ∑ χ : Bool × Bool, A *ᵥ commProjM A A' l χ v := by
        refine Finset.sum_congr rfl ?_
        intro χ _
        rcases χ with ⟨b1, b2⟩
        cases b1 <;> cases b2
        · have hp := commProjM_mem hA2 hA'2 hcomm hl0 (false, false) v
          have hAP : A *ᵥ commProjM A A' l (false, false) v =
              (-l) • commProjM A A' l (false, false) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).1
          have hA'P : A' *ᵥ commProjM A A' l (false, false) v =
              (-l) • commProjM A A' l (false, false) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).2
          rw [hA'P, hAP]
        · have hp : commProjM A A' l (false, true) v = 0 := by
            have hmem := commProjM_mem hA2 hA'2 hcomm hl0 (false, true) v
            rw [h2] at hmem
            simpa using hmem
          simp [hp]
        · have hp : commProjM A A' l (true, false) v = 0 := by
            have hmem := commProjM_mem hA2 hA'2 hcomm hl0 (true, false) v
            rw [h1] at hmem
            simpa using hmem
          simp [hp]
        · have hp := commProjM_mem hA2 hA'2 hcomm hl0 (true, true) v
          have hAP : A *ᵥ commProjM A A' l (true, true) v =
              l • commProjM A A' l (true, true) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).1
          have hA'P : A' *ᵥ commProjM A A' l (true, true) v =
              l • commProjM A A' l (true, true) v := by
            simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hp).2
          rw [hA'P, hAP]
    _ = A *ᵥ (∑ χ : Bool × Bool, commProjM A A' l χ v) :=
        (mulVec_finset_sum A _).symm
    _ = A *ᵥ v := by rw [sum_commProjM h2K v]

private theorem coeff_eq_zero_of_sum_smul {v : Fin 4 → (Fin 4 → K)} {a : Fin 4 → K}
    (ha : ∑ i, a i • v i = 0) {j : Fin 4} {w : Fin 4 → K}
    (hw : herm σ w (v j) = 1) (hz : ∀ i, i ≠ j → herm σ w (v i) = 0) : a j = 0 := by
  have h := congrArg (fun z => herm σ w z) ha
  simp only [herm_zero_right] at h
  rw [herm_finset_sum] at h
  simp only [herm_smul_right] at h
  rw [Finset.sum_eq_single j] at h
  · simpa [hw] using h
  · intro i _ hi
    rw [hz i hi, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ j) hnot

end FrameAux

theorem exists_antiFrame (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0)
    {A A' : Matrix (Fin 4) (Fin 4) K} {l : K} (hl : σ l * l = -1)
    (hAu : (A.map σ)ᵀ * A = 1) (hA'u : (A'.map σ)ᵀ * A' = 1) (hA2 : A * A = (l * l) • 1)
    (hA'2 : A' * A' = (l * l) • 1) (hcomm : A * A' = A' * A) (hne : A' ≠ A) (hne' : A' ≠ -A) :
    ∃ f₁ f₂ g₁ g₂ : Fin 4 → K, AntiFrame σ A A' l f₁ f₂ g₁ g₂ := by
  have hσc : ∀ c, σ (σ c) = c := hσ.invol
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hl
    exact one_ne_zero (neg_eq_zero.1 hl.symm)
  have hAiso : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y :=
    isometry_of_adjoint hAu
  have hA'iso : ∀ x y, herm σ (A' *ᵥ x) (A' *ᵥ y) = herm σ x y :=
    isometry_of_adjoint hA'u
  have hpp : commEigM A A' l (true, true) ≠ ⊥ ∨
      commEigM A A' l (false, false) ≠ ⊥ := by
    by_cases h1 : commEigM A A' l (true, true) = ⊥
    · by_cases h2 : commEigM A A' l (false, false) = ⊥
      · exact absurd (eq_neg_of_bot_pp_mm h2K hA2 hA'2 hcomm hl h1 h2) hne'
      · exact Or.inr h2
    · exact Or.inl h1
  have hpm : commEigM A A' l (true, false) ≠ ⊥ ∨
      commEigM A A' l (false, true) ≠ ⊥ := by
    by_cases h1 : commEigM A A' l (true, false) = ⊥
    · by_cases h2 : commEigM A A' l (false, true) = ⊥
      · exact absurd (eq_self_of_bot_pm_mp h2K hA2 hA'2 hcomm hl h1 h2) hne
      · exact Or.inr h2
    · exact Or.inl h1
  obtain ⟨f₁, g₁, hf₁W, hg₁W, hf₁g₁⟩ :=
    exists_pair_sgn hσ h2K hA2 hA'2 hcomm hl hAiso hA'iso (true, true) hpp
  obtain ⟨f₂, g₂, hf₂W, hg₂W, hf₂g₂⟩ :=
    exists_pair_sgn hσ h2K hA2 hA'2 hcomm hl hAiso hA'iso (true, false) hpm
  have hf₁A : A *ᵥ f₁ = l • f₁ := by
    simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hf₁W).1
  have hf₂A : A *ᵥ f₂ = l • f₂ := by
    simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hf₂W).1
  have hg₁A : A *ᵥ g₁ = (-l) • g₁ := by
    simpa [uSgn, negSgn] using mem_eigM.1 (Submodule.mem_inf.1 hg₁W).1
  have hg₂A : A *ᵥ g₂ = (-l) • g₂ := by
    simpa [uSgn, negSgn] using mem_eigM.1 (Submodule.mem_inf.1 hg₂W).1
  have hf₁B : A' *ᵥ f₁ = l • f₁ := by
    simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hf₁W).2
  have hf₂B : A' *ᵥ f₂ = (-l) • f₂ := by
    simpa [uSgn] using mem_eigM.1 (Submodule.mem_inf.1 hf₂W).2
  have hg₁B : A' *ᵥ g₁ = (-l) • g₁ := by
    simpa [uSgn, negSgn] using mem_eigM.1 (Submodule.mem_inf.1 hg₁W).2
  have hg₂B : A' *ᵥ g₂ = l • g₂ := by
    simpa [uSgn, negSgn] using mem_eigM.1 (Submodule.mem_inf.1 hg₂W).2
  have hf₁f₁ : herm σ f₁ f₁ = 0 :=
    herm_eigM_self hAiso h2K (norm_uSgn_mul hl true)
      (Submodule.mem_inf.1 hf₁W).1 (Submodule.mem_inf.1 hf₁W).1
  have hf₂f₂ : herm σ f₂ f₂ = 0 :=
    herm_eigM_self hAiso h2K (norm_uSgn_mul hl true)
      (Submodule.mem_inf.1 hf₂W).1 (Submodule.mem_inf.1 hf₂W).1
  have hg₁g₁ : herm σ g₁ g₁ = 0 :=
    herm_eigM_self hAiso h2K (norm_uSgn_mul hl false)
      (Submodule.mem_inf.1 hg₁W).1 (Submodule.mem_inf.1 hg₁W).1
  have hg₂g₂ : herm σ g₂ g₂ = 0 :=
    herm_eigM_self hAiso h2K (norm_uSgn_mul hl false)
      (Submodule.mem_inf.1 hg₂W).1 (Submodule.mem_inf.1 hg₂W).1
  have hf₁f₂ : herm σ f₁ f₂ = 0 :=
    herm_commEigM_eq_zero hAiso hA'iso h2K hl (by decide) hf₁W hf₂W
  have hf₁g₂ : herm σ f₁ g₂ = 0 :=
    herm_commEigM_eq_zero hAiso hA'iso h2K hl (by decide) hf₁W hg₂W
  have hf₂g₁ : herm σ f₂ g₁ = 0 :=
    herm_commEigM_eq_zero hAiso hA'iso h2K hl (by decide) hf₂W hg₁W
  have hg₁g₂ : herm σ g₁ g₂ = 0 :=
    herm_commEigM_eq_zero hAiso hA'iso h2K hl (by decide) hg₁W hg₂W
  have hg₁f₁ : herm σ g₁ f₁ = 1 := by
    rw [herm_conj σ hσc f₁ g₁, hf₁g₁, map_one]
  have hg₂f₂ : herm σ g₂ f₂ = 1 := by
    rw [herm_conj σ hσc f₂ g₂, hf₂g₂, map_one]
  have hf₂f₁ : herm σ f₂ f₁ = 0 := by
    rw [herm_conj σ hσc f₁ f₂, hf₁f₂, map_zero]
  have hg₂f₁ : herm σ g₂ f₁ = 0 := by
    rw [herm_conj σ hσc f₁ g₂, hf₁g₂, map_zero]
  have hg₁f₂ : herm σ g₁ f₂ = 0 := by
    rw [herm_conj σ hσc f₂ g₁, hf₂g₁, map_zero]
  have hg₂g₁ : herm σ g₂ g₁ = 0 := by
    rw [herm_conj σ hσc g₁ g₂, hg₁g₂, map_zero]
  have hli : LinearIndependent K ![f₁, f₂, g₁, g₂] := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : a 0 = 0 :=
      coeff_eq_zero_of_sum_smul ha (j := 0) (w := g₁) (by simpa using hg₁f₁)
        (by
          intro i hi
          fin_cases i
          · exact absurd rfl hi
          · simpa using hg₁f₂
          · simpa using hg₁g₁
          · simpa using hg₁g₂)
    have h2 : a 2 = 0 :=
      coeff_eq_zero_of_sum_smul ha (j := 2) (w := f₁) (by simpa using hf₁g₁)
        (by
          intro i hi
          fin_cases i
          · simpa using hf₁f₁
          · simpa using hf₁f₂
          · exact absurd rfl hi
          · simpa using hf₁g₂)
    have h1 : a 1 = 0 :=
      coeff_eq_zero_of_sum_smul ha (j := 1) (w := g₂) (by simpa using hg₂f₂)
        (by
          intro i hi
          fin_cases i
          · simpa using hg₂f₁
          · exact absurd rfl hi
          · simpa using hg₂g₁
          · simpa using hg₂g₂)
    have h3 : a 3 = 0 :=
      coeff_eq_zero_of_sum_smul ha (j := 3) (w := f₂) (by simpa using hf₂g₂)
        (by
          intro i hi
          fin_cases i
          · simpa using hf₂f₁
          · simpa using hf₂f₂
          · simpa using hf₂g₁
          · exact absurd rfl hi)
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hcard : Fintype.card (Fin 4) = Module.finrank K (Fin 4 → K) := by
    simp [Module.finrank_fintype_fun_eq_card]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = ![f₁, f₂, g₁, g₂] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨f₁, f₂, g₁, g₂, ?_⟩
  exact
    { af₁ := hf₁A
      af₂ := hf₂A
      ag₁ := hg₁A
      ag₂ := hg₂A
      bf₁ := hf₁B
      bf₂ := hf₂B
      bg₁ := hg₁B
      bg₂ := hg₂B
      f₁g₁ := hf₁g₁
      f₂g₂ := hf₂g₂
      f₁f₁ := hf₁f₁
      f₂f₂ := hf₂f₂
      g₁g₁ := hg₁g₁
      g₂g₂ := hg₂g₂
      f₁f₂ := hf₁f₂
      f₁g₂ := hf₁g₂
      f₂g₁ := hf₂g₁
      g₁g₂ := hg₁g₂
      span := by
        intro v
        refine ⟨b.repr v 0, b.repr v 1, b.repr v 2, b.repr v 3, ?_⟩
        have hsum := b.sum_repr v
        rw [Fin.sum_univ_four] at hsum
        rw [hb] at hsum
        simpa using hsum.symm }

end CFSG.LocalAnalysis.WeakClosure81.UOuter
