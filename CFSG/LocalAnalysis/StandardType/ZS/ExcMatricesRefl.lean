module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.Basic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K] {n : ℕ}

private lemma pijMat_row_i {i j : Fin n} (hij : i ≠ j) (α : K) (c : Fin n) :
    pijMat i j α i c = if c = j then α else 0 := by
  simp [pijMat, hij]

private lemma pijMat_row_j {i j : Fin n} (hij : i ≠ j) (α : K) (c : Fin n) :
    pijMat i j α j c = if c = i then α⁻¹ else 0 := by
  simp [pijMat, Ne.symm hij]

private lemma pijMat_row_other {i j : Fin n} (_hij : i ≠ j) (α : K) {r : Fin n}
    (hri : r ≠ i) (hrj : r ≠ j) (c : Fin n) :
    pijMat i j α r c = if r = c then 1 else 0 := by
  simp [pijMat, hri, hrj]

theorem pijMat_mul_self {i j : Fin n} (hij : i ≠ j) {α : K} (hα : α ≠ 0) :
    pijMat i j α * pijMat i j α = 1 := by
  ext r c
  rw [Matrix.mul_apply]
  by_cases hri : r = i
  · subst r
    simp_rw [pijMat_row_i hij α]
    rw [show (∑ k, (if k = j then α else 0) * pijMat i j α k c) = α * pijMat i j α j c by
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp]
    rw [pijMat_row_j hij α c, Matrix.one_apply]
    by_cases hc : c = i
    · subst c
      simp [mul_inv_cancel₀ hα]
    · rw [if_neg hc, if_neg (Ne.symm hc)]
      simp
  · by_cases hrj : r = j
    · subst r
      simp_rw [pijMat_row_j hij α]
      rw [show (∑ k, (if k = i then α⁻¹ else 0) * pijMat i j α k c) =
          α⁻¹ * pijMat i j α i c by
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq']
        simp]
      rw [pijMat_row_i hij α c, Matrix.one_apply]
      by_cases hc : c = j
      · subst c
        simp [inv_mul_cancel₀ hα]
      · rw [if_neg hc, if_neg (Ne.symm hc)]
        simp
    · simp_rw [pijMat_row_other hij α hri hrj]
      rw [show (∑ k, (if r = k then (1 : K) else 0) * pijMat i j α k c) = pijMat i j α r c by
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp]
      rw [pijMat_row_other hij α hri hrj c, Matrix.one_apply]

theorem pijMat_mul_pijMat {i j : Fin n} (hij : i ≠ j) (α β : K) :
    pijMat i j α * pijMat i j β =
      Matrix.diagonal fun k => if k = i then α * β⁻¹ else if k = j then α⁻¹ * β else 1 := by
  ext r c
  rw [Matrix.mul_apply]
  by_cases hri : r = i
  · subst r
    simp_rw [pijMat_row_i hij α]
    rw [show (∑ k, (if k = j then α else 0) * pijMat i j β k c) = α * pijMat i j β j c by
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp]
    rw [pijMat_row_j hij β c, Matrix.diagonal_apply]
    by_cases hc : c = i
    · subst c; simp
    · rw [if_neg hc, if_neg (Ne.symm hc)]; simp
  · by_cases hrj : r = j
    · subst r
      simp_rw [pijMat_row_j hij α]
      rw [show (∑ k, (if k = i then α⁻¹ else 0) * pijMat i j β k c) = α⁻¹ * pijMat i j β i c by
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq']
        simp]
      rw [pijMat_row_i hij β c, Matrix.diagonal_apply]
      by_cases hc : c = j
      · subst c; simp [hij, hij.symm]
      · rw [if_neg hc, if_neg (Ne.symm hc)]; simp
    · simp_rw [pijMat_row_other hij α hri hrj]
      rw [show (∑ k, (if r = k then (1 : K) else 0) * pijMat i j β k c) = pijMat i j β r c by
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp]
      rw [pijMat_row_other hij β hri hrj c, Matrix.diagonal_apply]
      by_cases hrc : r = c
      · subst c; simp [hri, hrj]
      · rw [if_neg hrc, if_neg hrc]

theorem diagSignMat_mul_self (i : Fin n) :
    (diagSignMat i : Matrix (Fin n) (Fin n) K) * diagSignMat i = 1 := by
  rw [diagSignMat, Matrix.diagonal_mul_diagonal]
  rw [show (fun j : Fin n => (if j = i then (-1 : K) else 1) * (if j = i then -1 else 1)) =
        fun _ => (1 : K) by
    funext j
    by_cases hj : j = i <;> simp [hj]]
  exact Matrix.diagonal_one

theorem halfOnesMat_mul_self (h2 : (2 : K) ≠ 0) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) K) * halfOnesMat 4 = 1 := by
  ext r c
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [halfOnesMat, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_one]
  rw [Fin.sum_univ_four]
  fin_cases r <;> fin_cases c <;> simp <;> field_simp <;> ring

end Matrices

section Basis

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}
  (f : Module.Basis (Fin n) K V)

theorem toMatrix_coe_mul (x y : V ≃ₗ[K] V) :
    LinearMap.toMatrix f f ((x * y : V ≃ₗ[K] V) : V →ₗ[K] V) =
      LinearMap.toMatrix f f (x : V →ₗ[K] V) * LinearMap.toMatrix f f (y : V →ₗ[K] V) := by
  rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

theorem eq_of_toMatrix_eq {x y : V ≃ₗ[K] V}
    (h : LinearMap.toMatrix f f (x : V →ₗ[K] V) = LinearMap.toMatrix f f (y : V →ₗ[K] V)) :
    x = y := by
  apply LinearEquiv.toLinearMap_injective
  exact (LinearMap.toMatrix f f).injective h

theorem orderOf_toMatrix (x : V ≃ₗ[K] V) :
    orderOf (LinearMap.toMatrix f f (x : V →ₗ[K] V)) = orderOf x := by
  let φ : (V ≃ₗ[K] V) →* Matrix (Fin n) (Fin n) K :=
    { toFun := fun y => LinearMap.toMatrix f f (y : V →ₗ[K] V)
      map_one' := by simp
      map_mul' := fun y z => by rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul] }
  have hφ : Function.Injective φ := fun x y h => eq_of_toMatrix_eq f h
  exact orderOf_injective φ hφ x

theorem exists_mem_basisClosure_toMatrix_eq {S : Set (Matrix (Fin n) (Fin n) K)}
    {M : Matrix (Fin n) (Fin n) K} (hM : M ∈ S) (hdet : IsUnit M.det) :
    ∃ g ∈ basisClosure f S, LinearMap.toMatrix f f (g : V →ₗ[K] V) = M := by
  refine ⟨Matrix.toLinearEquiv f M hdet, Subgroup.subset_closure ?_, ?_⟩
  · show LinearMap.toMatrix f f ((Matrix.toLinearEquiv f M hdet : V ≃ₗ[K] V) : V →ₗ[K] V) ∈ S
    rw [show ((Matrix.toLinearEquiv f M hdet : V ≃ₗ[K] V) : V →ₗ[K] V) =
        Matrix.toLin f f M from rfl, LinearMap.toMatrix_toLin]
    exact hM
  · show LinearMap.toMatrix f f ((Matrix.toLinearEquiv f M hdet : V ≃ₗ[K] V) : V →ₗ[K] V) = M
    rw [show ((Matrix.toLinearEquiv f M hdet : V ≃ₗ[K] V) : V →ₗ[K] V) =
        Matrix.toLin f f M from rfl, LinearMap.toMatrix_toLin]

end Basis

section Refl

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {t : U ≃ₗ[ZMod p] U}

private lemma toMatrix_apply_basis {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {g : U →ₗ[ZMod p] U} {M : Matrix (Fin n) (Fin n) (ZMod p)}
    (hg : LinearMap.toMatrix f f g = M) (c : Fin n) :
    g (f c) = ∑ r, M r c • f r := by
  rw [← Matrix.toLin_toMatrix f f g, hg, Matrix.toLin_self]

private lemma range_eq_span_of_basis {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {g : U →ₗ[ZMod p] U} {v : U}
    (hgen : ∀ c, g (f c) ∈ Submodule.span (ZMod p) {v})
    (hv : v ∈ LinearMap.range g) :
    LinearMap.range g = Submodule.span (ZMod p) {v} := by
  have h1 : LinearMap.range g = Submodule.span (ZMod p) (g '' Set.range f) := by
    rw [LinearMap.range_eq_map, ← f.span_eq, Submodule.map_span]
  rw [h1]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact hgen c
  · rw [Submodule.span_le]
    rintro _ hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [← h1]
    exact hv

private lemma pijMat_action_i {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n}
    (hij : i ≠ j) {α : ZMod p}
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = pijMat i j α) :
    (t : U →ₗ[ZMod p] U) (f i) = α⁻¹ • f j := by
  rw [toMatrix_apply_basis f ht i, Finset.sum_eq_single j]
  · rw [pijMat_row_j hij α i]; simp
  · intro r _ hrj
    by_cases hri : r = i
    · subst r; rw [pijMat_row_i hij α i]; simp only [hij, if_false, zero_smul]
    · rw [pijMat_row_other hij α hri hrj i]; simp [hri]
  · intro h; exact absurd (Finset.mem_univ j) h

private lemma pijMat_action_j {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n}
    (hij : i ≠ j) {α : ZMod p}
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = pijMat i j α) :
    (t : U →ₗ[ZMod p] U) (f j) = α • f i := by
  rw [toMatrix_apply_basis f ht j, Finset.sum_eq_single i]
  · rw [pijMat_row_i hij α j]; simp
  · intro r _ hri
    by_cases hrj : r = j
    · subst r; rw [pijMat_row_j hij α j]; simp [Ne.symm hij]
    · rw [pijMat_row_other hij α hri hrj j]; simp [hrj]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma pijMat_sub_action {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n}
    (hij : i ≠ j) {α : ZMod p} (hα : α ≠ 0)
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = pijMat i j α) :
    ∀ c, ((t : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) (f c) ∈
      Submodule.span (ZMod p) {α • f i - f j} := by
  intro c
  by_cases hci : c = i
  · subst c
    rw [LinearMap.sub_apply, LinearMap.id_apply, pijMat_action_i f hij ht]
    have hroot : α⁻¹ • f j - f i = -(α⁻¹ • (α • f i - f j)) := by
      have h1 : α⁻¹ • (α • f i - f j) = f i - α⁻¹ • f j := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hα, one_smul]
      rw [h1]
      abel
    rw [hroot]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton _)))
  · by_cases hcj : c = j
    · subst c
      rw [LinearMap.sub_apply, LinearMap.id_apply, pijMat_action_j f hij ht]
      exact Submodule.subset_span (Set.mem_singleton _)
    · have hc : (t : U →ₗ[ZMod p] U) (f c) = f c := by
        rw [toMatrix_apply_basis f ht c, Finset.sum_eq_single c]
        · rw [pijMat_row_other hij α hci hcj c]; simp
        · intro r _ hrc
          by_cases hri : r = i
          · subst r; rw [pijMat_row_i hij α c]; simp [hcj]
          · by_cases hrj : r = j
            · subst r; rw [pijMat_row_j hij α c]; simp [hci]
            · rw [pijMat_row_other hij α hri hrj c]; simp [hrc]
        · intro h; exact absurd (Finset.mem_univ c) h
      rw [LinearMap.sub_apply, LinearMap.id_apply, hc, sub_self]
      exact Submodule.zero_mem _

private lemma pijMat_root_ne {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n}
    (hij : i ≠ j) {α : ZMod p} (hα : α ≠ 0) : α • f i - f j ≠ 0 := by
  intro h
  have hsum : ∑ k : Fin n, (if k = i then α else if k = j then (-1 : ZMod p) else 0) • f k = 0 := by
    have hsplit : ∑ k : Fin n, (if k = i then α else if k = j then (-1 : ZMod p) else 0) • f k =
        α • f i - f j := by
      rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ i)]
      rw [Finset.sum_eq_single j]
      · simp [Ne.symm hij, sub_eq_add_neg, add_comm]
      · intro k hk hkj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hk
        simp [hk, hkj]
      · intro hk
        exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, by simp [Ne.symm hij]⟩) hk
    rw [hsplit, h]
  have h0 := Fintype.linearIndependent_iff.mp f.linearIndependent
    (fun k : Fin n => if k = i then α else if k = j then (-1 : ZMod p) else 0) hsum i
  rw [if_pos rfl] at h0
  exact hα h0

theorem isRefl_of_toMatrix_eq_pijMat {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n}
    (hij : i ≠ j) {α : ZMod p} (hα : α ≠ 0)
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = pijMat i j α) : IsRefl p t := by
  constructor
  · apply eq_of_toMatrix_eq f
    rw [toMatrix_coe_mul f, ht, pijMat_mul_self hij hα]
    simp
  · have hrange : LinearMap.range ((t : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) =
        Submodule.span (ZMod p) {α • f i - f j} :=
      range_eq_span_of_basis f (pijMat_sub_action f hij hα ht) ⟨f j, by
        rw [LinearMap.sub_apply, LinearMap.id_apply, pijMat_action_j f hij ht]⟩
    rw [hrange]
    exact finrank_span_singleton (pijMat_root_ne f hij hα)

private lemma diagSignMat_action {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i : Fin n}
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = diagSignMat i) (c : Fin n) :
    (t : U →ₗ[ZMod p] U) (f c) = (if c = i then -1 else 1) • f c := by
  rw [toMatrix_apply_basis f ht c, Finset.sum_eq_single c]
  · simp [diagSignMat]
  · intro r _ hrc
    simp [diagSignMat, hrc]
  · intro h; exact absurd (Finset.mem_univ c) h

theorem isRefl_of_toMatrix_eq_diagSignMat (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {i : Fin n}
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = diagSignMat i) : IsRefl p t := by
  have hφ : (2 • f.coord i) (f i) = 2 := by simp
  have ht_ref : t = Module.reflection hφ := by
    refine f.ext' fun c => ?_
    change (t : U →ₗ[ZMod p] U) (f c) = (Module.reflection hφ) (f c)
    rw [diagSignMat_action f ht c, Module.reflection_apply]
    by_cases hci : c = i
    · subst c
      simp [two_smul, sub_eq_add_neg, add_smul, one_smul]
    · simp [hci, Ne.symm hci, f.coord_apply]
  rw [ht_ref]
  exact isRefl_reflection hp hφ

end Refl

end CFSG.StandardType.ZS
