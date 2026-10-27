module

public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSUForm
public import CFSG.Fischer.Classification.PartII.Herm.Classify

public section

namespace CFSG.StandardType

open Matrix Module CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification

section Basis

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem herm_single_one_single_one {m : ℕ} (i j : Fin m) :
    herm σ (Pi.single i (1 : F)) (Pi.single j 1) = if i = j then 1 else 0 := by
  rw [herm_def, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, map_one, one_mul, Pi.single_apply]
  · intro t _ ht
    rw [Pi.single_eq_of_ne ht, map_zero, zero_mul]
  · simp

theorem exists_ggU_dual_family (hσ : IsUnitaryInvolution σ) {N : Matrix (Fin n) (Fin n) F}
    (hN : N * N = 0) (hadj : ∀ x y, ggUForm σ (N *ᵥ x) y = ggUForm σ x (N *ᵥ y)) :
    ∃ l : ℕ, l = finrank F (LinearMap.range N.mulVecLin) ∧ ∃ w : Fin l → (Fin n → F),
      (∀ i j, ggUForm σ (w i) (N *ᵥ w j) = if i = j then 1 else 0) ∧
      ∀ i j, ggUForm σ (w i) (w j) = 0 := by
  classical
  set l := finrank F (LinearMap.range N.mulVecLin) with hl
  have hNN : ∀ x, N *ᵥ (N *ᵥ x) = 0 := fun x => by
    rw [Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  set K := LinearMap.ker N.mulVecLin with hK
  obtain ⟨W, hW⟩ := K.exists_isCompl
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have h2 := Submodule.finrank_add_eq_of_isCompl hW
  rw [← hK] at h1
  have hWl : finrank F W = l := by omega
  let β : W → W → F := fun x y => ggUForm σ (x : Fin n → F) (N *ᵥ (y : Fin n → F))
  have hβ : Herm.IsHermForm σ β :=
    { add_left := fun x x' y => by simp only [β, Submodule.coe_add, ggUForm_add_left]
      smul_left := fun c x y => by simp only [β, Submodule.coe_smul, ggUForm_smul_left]
      conj := fun x y => by
        simp only [β]
        rw [ggUForm_conj hσ.invol (N *ᵥ (x : Fin n → F)) (y : Fin n → F), hadj] }
  have hnd : ∀ x : W, (∀ y : W, β x y = 0) → x = 0 := by
    intro x hx
    have hNx : N *ᵥ (x : Fin n → F) = 0 := by
      refine eq_zero_of_ggUForm (σ := σ) fun v => ?_
      rw [hadj]
      have hv : v ∈ K ⊔ W := by rw [hW.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨κ, hκ, ω, hω, rfl⟩ := Submodule.mem_sup.mp hv
      have hκ0 : N *ᵥ κ = 0 := by simpa using (LinearMap.mem_ker.mp hκ)
      rw [Matrix.mulVec_add, ggUForm_add_right, hκ0, ggUForm_zero_right, zero_add]
      exact hx ⟨ω, hω⟩
    have hxK : (x : Fin n → F) ∈ K := LinearMap.mem_ker.mpr (by simpa using hNx)
    have hxKW : (x : Fin n → F) ∈ K ⊓ W := ⟨hxK, x.2⟩
    rw [hW.inf_eq_bot, Submodule.mem_bot] at hxKW
    exact Subtype.ext hxKW
  obtain ⟨e, he⟩ := exists_linearEquiv_herm_of_form hσ hβ hnd hWl
  let w₀ : Fin l → (Fin n → F) := fun i => ((e.symm (Pi.single i 1) : W) : Fin n → F)
  have hw₀ : ∀ i j, ggUForm σ (w₀ i) (N *ᵥ w₀ j) = if i = j then 1 else 0 := by
    intro i j
    have h := he (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, herm_single_one_single_one] at h
    exact h.symm
  have hyy : ∀ i j, ggUForm σ (N *ᵥ w₀ i) (N *ᵥ w₀ j) = 0 := fun i j => by
    rw [hadj, hNN, ggUForm_zero_right]
  have hyw : ∀ i j, ggUForm σ (N *ᵥ w₀ i) (w₀ j) = if i = j then 1 else 0 := fun i j => by
    rw [ggUForm_conj hσ.invol (w₀ j) (N *ᵥ w₀ i), hw₀]
    by_cases hij : i = j
    · rw [ite_eq_left hij.symm, ite_eq_left hij, map_one]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, map_zero]
  let g : Fin l → Fin l → F := fun i j => ggUForm σ (w₀ i) (w₀ j)
  have hg : ∀ i j, σ (g j i) = g i j := fun i j => (ggUForm_conj hσ.invol (w₀ j) (w₀ i)).symm
  have hτ : ∀ i, ∃ c, c + σ c = -g i i := fun i => hσ.trace_surj _ (by rw [map_neg, hg])
  choose τ hτ using hτ
  let t : Fin l → Fin l → F := fun i j => if j < i then -g j i else if i = j then τ i else 0
  let w : Fin l → (Fin n → F) := fun i => w₀ i + ∑ j, t i j • (N *ᵥ w₀ j)
  have hNw : ∀ i, N *ᵥ w i = N *ᵥ w₀ i := fun i => by
    simp only [w, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hNN, smul_zero,
      Finset.sum_const_zero, add_zero]
  refine ⟨l, hl, w, fun i j => ?_, fun i j => ?_⟩
  · rw [hNw, ggUForm_add_left, ggUForm_sum_smul_left]
    simp only [hyy, mul_zero, Finset.sum_const_zero, add_zero]
    exact hw₀ i j
  · have hexp : ggUForm σ (w i) (w j) = g i j + t j i + σ (t i j) := by
      simp only [w, ggUForm_add_left, ggUForm_add_right, ggUForm_sum_smul_left,
        ggUForm_sum_smul_right, hyy, hyw, hw₀, mul_zero, Finset.sum_const_zero, add_zero, mul_ite,
        mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    rw [hexp]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [t, ite_eq_left hij, ite_eq_right (not_lt.mpr hij.le), ite_eq_right hij.ne,
        map_zero, add_zero]
      ring
    · simp only [t, lt_irrefl, ite_false, ite_true]
      linear_combination hτ i
    · simp only [t, ite_eq_right (not_lt.mpr hij.le), ite_eq_right hij.ne, ite_eq_left hij,
        map_neg, hg]
      ring

theorem exists_ggU_middle_family (hσ : IsUnitaryInvolution σ) {l : ℕ} {w y : Fin l → (Fin n → F)}
    (hwy : ∀ i j, ggUForm σ (w i) (y j) = if i = j then 1 else 0)
    (hww : ∀ i j, ggUForm σ (w i) (w j) = 0) (hyy : ∀ i j, ggUForm σ (y i) (y j) = 0) :
    2 * l ≤ n ∧ ∃ v : Fin (n - 2 * l) → (Fin n → F),
      (∀ i j, ggUForm σ (v i) (v j) = if j = Fin.rev i then 1 else 0) ∧
      (∀ i j, ggUForm σ (w i) (v j) = 0) ∧ ∀ i j, ggUForm σ (y i) (v j) = 0 := by
  classical
  have hyw : ∀ i j, ggUForm σ (y i) (w j) = if i = j then 1 else 0 := fun i j => by
    rw [ggUForm_conj hσ.invol (w j) (y i), hwy]
    by_cases hij : i = j
    · rw [ite_eq_left hij.symm, ite_eq_left hij, map_one]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, map_zero]
  let Φ : (Fin n → F) →ₗ[F] (Fin l → F) × (Fin l → F) :=
    (LinearMap.pi fun i => ggUFormL σ (w i)).prod (LinearMap.pi fun i => ggUFormL σ (y i))
  have hΦ1 : ∀ x i, (Φ x).1 i = ggUForm σ (w i) x := fun x i => rfl
  have hΦ2 : ∀ x i, (Φ x).2 i = ggUForm σ (y i) x := fun x i => rfl
  let s : (Fin l → F) × (Fin l → F) → (Fin n → F) := fun pq =>
    ∑ j, pq.1 j • y j + ∑ j, pq.2 j • w j
  have hs : ∀ pq, Φ (s pq) = pq := by
    intro pq
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · rw [hΦ1]
      simp only [s, ggUForm_add_right, ggUForm_sum_smul_right, hwy, hww, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]
    · rw [hΦ2]
      simp only [s, ggUForm_add_right, ggUForm_sum_smul_right, hyy, hyw, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero, zero_add]
  have hsurj : LinearMap.range Φ = ⊤ := LinearMap.range_eq_top.mpr fun pq => ⟨s pq, hs pq⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, finrank_top, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hrn
  set M := LinearMap.ker Φ with hMdef
  have hMk : finrank F M = n - 2 * l := by omega
  refine ⟨by omega, ?_⟩
  let hM : M → M → F := fun x y => ggUForm σ (x : Fin n → F) (y : Fin n → F)
  have hhM : Herm.IsHermForm σ hM :=
    { add_left := fun x x' y => by simp only [hM, Submodule.coe_add, ggUForm_add_left]
      smul_left := fun c x y => by simp only [hM, Submodule.coe_smul, ggUForm_smul_left]
      conj := fun x y => ggUForm_conj hσ.invol _ _ }
  have hndM : ∀ x : M, (∀ y : M, hM x y = 0) → x = 0 := by
    intro x hx
    have hxM : Φ x = 0 := LinearMap.mem_ker.mp x.2
    have hwx : ∀ i, ggUForm σ (x : Fin n → F) (w i) = 0 := fun i => by
      rw [ggUForm_conj hσ.invol (w i), ← hΦ1, hxM, Prod.fst_zero, Pi.zero_apply, map_zero]
    have hyx : ∀ i, ggUForm σ (x : Fin n → F) (y i) = 0 := fun i => by
      rw [ggUForm_conj hσ.invol (y i), ← hΦ2, hxM, Prod.snd_zero, Pi.zero_apply, map_zero]
    refine Subtype.ext (eq_zero_of_ggUForm (σ := σ) fun v => ?_)
    have hm : v - s (Φ v) ∈ M := by rw [LinearMap.mem_ker, map_sub, hs, sub_self]
    have hv : v = (v - s (Φ v)) + s (Φ v) := by abel
    rw [hv, ggUForm_add_right]
    have h0 := hx ⟨_, hm⟩
    simp only [hM] at h0
    rw [h0, zero_add]
    simp only [s, ggUForm_add_right, ggUForm_sum_smul_right, hwx, hyx, mul_zero,
      Finset.sum_const_zero, add_zero]
  obtain ⟨e, he⟩ := exists_linearEquiv_herm_of_form hσ hhM hndM hMk
  obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  obtain ⟨P, hP⟩ := exists_wittMatrix_of σ (n := n - 2 * l) hu hω hω1
  let v : Fin (n - 2 * l) → (Fin n → F) := fun j =>
    ((e.symm (fun r => (P : Matrix (Fin (n - 2 * l)) (Fin (n - 2 * l)) F) r j) : M) : Fin n → F)
  have hvM : ∀ j, Φ (v j) = 0 := fun j => LinearMap.mem_ker.mp (e.symm _).2
  refine ⟨v, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · have h := he (e.symm (fun r => (P : Matrix (Fin (n - 2 * l)) (Fin (n - 2 * l)) F) r i))
      (e.symm (fun r => (P : Matrix (Fin (n - 2 * l)) (Fin (n - 2 * l)) F) r j))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    change ggUForm σ (v i) (v j) = _
    rw [show ggUForm σ (v i) (v j) = hM _ _ from rfl, ← h]
    have h2 := congrFun (congrFun hP i) j
    simp only [Matrix.mul_apply, conjTr, transpose_apply, map_apply] at h2
    rw [herm_def, h2]
    simp only [antidiag, of_apply]
  · rw [← hΦ1, hvM, Prod.fst_zero, Pi.zero_apply]
  · rw [← hΦ2, hvM, Prod.snd_zero, Pi.zero_apply]

end Basis

end CFSG.StandardType
