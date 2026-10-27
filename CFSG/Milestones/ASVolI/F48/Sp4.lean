module

public import CFSG.Milestones.ASVolI.F48.L3
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open

section Sp4Core

variable {K : Type} [Field K]

open Matrix in
@[expose] def burnsideF48_spElt (M M' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (h1 : M * M' = 1)
    (h2 : M' * M = 1) (hsp : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0) :
    StatedSp 2 K :=
  ⟨⟨M, M', h1, h2⟩, CFSG.Open.StatedAPI.mem_statedSp_iff.2 hsp⟩

def burnsideF48_spH (a b : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (Matrix.diagonal ![a, b]) 0 0 (Matrix.diagonal ![a⁻¹, b⁻¹])

def burnsideF48_spN (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 0 !![0, 0; 0, 1] 1

def burnsideF48_spNinv (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 0 (-!![0, 0; 0, 1]) 1

def burnsideF48_spW (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 (-1) 1 0

def burnsideF48_spWinv (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem burnsideF48_spH_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    burnsideF48_spH a b * burnsideF48_spH a⁻¹ b⁻¹ = 1 := by
  simp only [burnsideF48_spH, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal,
    zero_mul, mul_zero, add_zero, zero_add, inv_inv]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_, rfl, rfl, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb]

open Matrix in
theorem burnsideF48_spH_symp {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (burnsideF48_spH a b)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * burnsideF48_spH a b =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  simp only [burnsideF48_spH, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.diagonal_transpose, Matrix.transpose_zero, Matrix.diagonal_mul_diagonal,
    zero_mul, mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_neg]
  rw [Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, rfl⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb]

theorem burnsideF48_spH_mul' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    burnsideF48_spH a⁻¹ b⁻¹ * burnsideF48_spH a b = 1 := by
  have := burnsideF48_spH_mul (inv_ne_zero ha) (inv_ne_zero hb)
  rwa [inv_inv, inv_inv] at this

open Matrix in
theorem burnsideF48_E_transpose : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideF48_spN_mul : burnsideF48_spN K * burnsideF48_spNinv K = 1 := by
  simp only [burnsideF48_spN, burnsideF48_spNinv, Matrix.fromBlocks_multiply, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, add_neg_cancel]
  exact Matrix.fromBlocks_one

theorem burnsideF48_spNinv_mul : burnsideF48_spNinv K * burnsideF48_spN K = 1 := by
  simp only [burnsideF48_spN, burnsideF48_spNinv, Matrix.fromBlocks_multiply, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, neg_add_cancel]
  exact Matrix.fromBlocks_one

open Matrix in
theorem burnsideF48_spN_symp :
    (burnsideF48_spN K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * burnsideF48_spN K =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  simp only [burnsideF48_spN, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_one, Matrix.transpose_zero, burnsideF48_E_transpose, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg,
    neg_add_cancel]

theorem burnsideF48_spW_mul : burnsideF48_spW K * burnsideF48_spWinv K = 1 := by
  simp only [burnsideF48_spW, burnsideF48_spWinv, Matrix.fromBlocks_multiply, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact Matrix.fromBlocks_one

theorem burnsideF48_spWinv_mul : burnsideF48_spWinv K * burnsideF48_spW K = 1 := by
  simp only [burnsideF48_spW, burnsideF48_spWinv, Matrix.fromBlocks_multiply, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact Matrix.fromBlocks_one

open Matrix in
theorem burnsideF48_spW_symp :
    (burnsideF48_spW K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * burnsideF48_spW K =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  simp only [burnsideF48_spW, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_neg, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

@[expose] def burnsideF48_spHElt (a b : Kˣ) : StatedSp 2 K :=
  burnsideF48_spElt (burnsideF48_spH (a : K) (b : K)) (burnsideF48_spH (a : K)⁻¹ (b : K)⁻¹)
    (burnsideF48_spH_mul a.ne_zero b.ne_zero) (burnsideF48_spH_mul' a.ne_zero b.ne_zero)
    (burnsideF48_spH_symp a.ne_zero b.ne_zero)

@[expose] def burnsideF48_spNElt (K : Type) [Field K] : StatedSp 2 K :=
  burnsideF48_spElt (burnsideF48_spN K) (burnsideF48_spNinv K) burnsideF48_spN_mul
    burnsideF48_spNinv_mul burnsideF48_spN_symp

@[expose] def burnsideF48_spWElt (K : Type) [Field K] : StatedSp 2 K :=
  burnsideF48_spElt (burnsideF48_spW K) (burnsideF48_spWinv K) burnsideF48_spW_mul
    burnsideF48_spWinv_mul burnsideF48_spW_symp

open Matrix in
theorem burnsideF48_spH_mulVec_inl (a b : K) (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (burnsideF48_spH a b *ᵥ v) (Sum.inl i) = ![a, b] i * v (Sum.inl i) := by
  simp [burnsideF48_spH, Matrix.fromBlocks_mulVec, Matrix.mulVec_diagonal]

open Matrix in
theorem burnsideF48_spH_mulVec_inr (a b : K) (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (burnsideF48_spH a b *ᵥ v) (Sum.inr i) = ![a⁻¹, b⁻¹] i * v (Sum.inr i) := by
  simp [burnsideF48_spH, Matrix.fromBlocks_mulVec, Matrix.mulVec_diagonal]

open Matrix in
theorem burnsideF48_spN_mulVec_inl (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (burnsideF48_spN K *ᵥ v) (Sum.inl i) = v (Sum.inl i) := by
  simp [burnsideF48_spN, Matrix.fromBlocks_mulVec]

open Matrix in
theorem burnsideF48_spN_mulVec_inr (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (burnsideF48_spN K *ᵥ v) (Sum.inr i) = v (Sum.inr i) + (if i = 1 then v (Sum.inl 1) else 0) := by
  fin_cases i <;> simp [burnsideF48_spN, Matrix.fromBlocks_mulVec, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, add_comm]

open Matrix in
theorem burnsideF48_spNinv_mulVec_inl (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (burnsideF48_spNinv K *ᵥ v) (Sum.inl i) = v (Sum.inl i) := by
  simp [burnsideF48_spNinv, Matrix.fromBlocks_mulVec]

open Matrix in
theorem burnsideF48_spNinv_mulVec_inr (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (burnsideF48_spNinv K *ᵥ v) (Sum.inr i) =
      v (Sum.inr i) - (if i = 1 then v (Sum.inl 1) else 0) := by
  fin_cases i <;> simp [burnsideF48_spNinv, Matrix.fromBlocks_mulVec, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, sub_eq_add_neg, add_comm]

open Matrix in
theorem burnsideF48_spW_mulVec_inr (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (burnsideF48_spW K *ᵥ v) (Sum.inr i) = v (Sum.inl i) := by
  simp [burnsideF48_spW, Matrix.fromBlocks_mulVec]

theorem burnsideF48_spH_mul_spN {a : K} (ha : a ≠ 0) :
    burnsideF48_spH a 1 * burnsideF48_spN K = burnsideF48_spN K * burnsideF48_spH a 1 := by
  simp only [burnsideF48_spH, burnsideF48_spN, Matrix.fromBlocks_multiply, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.fromBlocks_inj]
  refine ⟨rfl, rfl, ?_, rfl⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two]

theorem burnsideF48_spH_mul_spW (a b : K) :
    burnsideF48_spH a b * burnsideF48_spW K = burnsideF48_spW K * burnsideF48_spH a⁻¹ b⁻¹ := by
  simp only [burnsideF48_spH, burnsideF48_spW, Matrix.fromBlocks_multiply, zero_mul, mul_zero,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, inv_inv]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_spElt_mem_stabilizer {M M' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {h1 : M * M' = 1} {h2 : M' * M = 1}
    {hsp : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0}
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hM : ∀ v ∈ W, M *ᵥ v ∈ W)
    (hM' : ∀ v ∈ W, M' *ᵥ v ∈ W) :
    burnsideF48_spElt M M' h1 h2 hsp ∈ stabilizer 2 K W :=
  mem_stabilizer_of_mulVec_mem hM hM'

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem burnsideF48_spNElt_mem_stab_one :
    burnsideF48_spNElt K ∈ stabilizer 2 K (flag 2 K 1) := by
  refine burnsideF48_spElt_mem_stabilizer ?_ ?_ <;>
  · intro v hv
    rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hv ⊢
    obtain ⟨h1, h2⟩ := hv
    have h11 : v (Sum.inl 1) = 0 := h2 1 (by decide)
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · first
        | rw [burnsideF48_spN_mulVec_inr, h1 j, h11]
        | rw [burnsideF48_spNinv_mulVec_inr, h1 j, h11]
      simp
    · first
        | rw [burnsideF48_spN_mulVec_inl, h2 j hj]
        | rw [burnsideF48_spNinv_mulVec_inl, h2 j hj]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_sp_stab_apply {g : StatedSp 2 K} {W : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hg : g ∈ stabilizer 2 K W) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ W) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈ W := by
  have := Submodule.mem_map_of_mem (f := Matrix.mulVecLin ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hv
  rwa [mem_stabilizer.1 hg] at this

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_spNElt_not_mem_stab_two :
    burnsideF48_spNElt K ∉ stabilizer 2 K (flag 2 K 2) := by
  intro h
  have hv : (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 := by
    rw [mem_flag_of_le le_rfl, mem_isoFlag]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have := j.isLt
    omega
  have h1 := burnsideF48_sp_stab_apply h hv
  rw [mem_flag_of_le le_rfl, mem_isoFlag] at h1
  have h2 := h1.1 1
  change (burnsideF48_spN K *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K)) (Sum.inr 1) = 0 at h2
  rw [burnsideF48_spN_mulVec_inr] at h2
  simp at h2

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_spH_maps_isoFlag (a b : K) {i : ℕ} {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ∈ isoFlag 2 K i) : burnsideF48_spH a b *ᵥ v ∈ isoFlag 2 K i := by
  rw [mem_isoFlag] at hv ⊢
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · rw [burnsideF48_spH_mulVec_inr, hv.1 j, mul_zero]
  · rw [burnsideF48_spH_mulVec_inl, hv.2 j hj, mul_zero]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem burnsideF48_spHElt_mem_stab (a b : Kˣ) {i : ℕ} (hi : i ≤ 2) :
    burnsideF48_spHElt a b ∈ stabilizer 2 K (flag 2 K i) := by
  refine burnsideF48_spElt_mem_stabilizer ?_ ?_ <;>
  · intro v hv
    rw [mem_flag_of_le hi] at hv ⊢
    exact burnsideF48_spH_maps_isoFlag _ _ hv

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_sp_stab_one_eig {g : StatedSp 2 K} (hg : g ∈ stabilizer 2 K (flag 2 K 1)) :
    ∃ c : K, ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) = c • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) := by
  have he0 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 := by
    rw [mem_flag_of_le (by norm_num), mem_isoFlag]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
    simp [Pi.single_apply, hj0]
  have hmem := burnsideF48_sp_stab_apply hg he0
  rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hmem
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨(((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
    Pi.single (Sum.inl 0) 1) (Sum.inl 0), ?_⟩
  funext i
  rcases i with j | j
  · by_cases hj : j = 0
    · subst hj
      simp
    · rw [h2 j (Nat.one_le_iff_ne_zero.mpr fun h => hj (Fin.ext h))]
      simp [Pi.single_apply, hj]
  · rw [h1 j]
    simp

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_spWElt_ne_mul {k l k' : StatedSp 2 K}
    (hk : k ∈ stabilizer 2 K (flag 2 K 1)) (hl : l ∈ stabilizer 2 K (flag 2 K 2))
    (hk' : k' ∈ stabilizer 2 K (flag 2 K 1)) : burnsideF48_spWElt K ≠ k * l * k' := by
  intro hw
  set e₀ : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 with he₀
  have he0 : e₀ ∈ flag 2 K 1 := by
    rw [mem_flag_of_le (by norm_num), mem_isoFlag]
    refine ⟨fun j => by simp [he₀], fun j hj => ?_⟩
    have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
    simp [he₀, Pi.single_apply, hj0]
  have h1 := burnsideF48_sp_stab_apply hk' he0
  have h2 : (((k' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e₀) ∈
      flag 2 K 2 := by
    rw [mem_flag_of_le (by norm_num), mem_isoFlag] at h1 ⊢
    exact ⟨h1.1, fun j hj => absurd hj (by have := j.isLt; omega)⟩
  have h3 := burnsideF48_sp_stab_apply hl h2
  have hu0 : (((l : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (((k' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e₀))
        (Sum.inr 0) = 0 := by
    rw [mem_flag_of_le le_rfl, mem_isoFlag] at h3
    exact h3.1 0
  obtain ⟨c, hc⟩ := burnsideF48_sp_stab_one_eig ((stabilizer 2 K (flag 2 K 1)).inv_mem hk)
  have h4 := burnsideF4h_cl_sp_inv_f0 hc (((l : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (((k' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e₀))
  rw [inv_inv, hu0, mul_zero] at h4
  have h5 : (burnsideF48_spW K) *ᵥ e₀ = ((k : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (((l : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (((k' : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e₀)) := by
    have h6 : (burnsideF48_spW K) = ((k : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((l : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((k' : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      have := congrArg (fun g : StatedSp 2 K => ((g : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hw
      simpa [burnsideF48_spWElt, burnsideF48_spElt] using this
    rw [h6, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h7 : ((burnsideF48_spW K) *ᵥ e₀) (Sum.inr 0) = 1 := by
    rw [burnsideF48_spW_mulVec_inr]
    simp [he₀]
  rw [h5] at h7
  rw [h4] at h7
  exact zero_ne_one h7

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem burnsideF48_sp_proj_eq_mat {x y : StatedSp 2 K} (h : proj 2 K x = proj 2 K y) :
    ∃ c : K, ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSp 2 K) x y).1 h
  exact ⟨(u : K), hu⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_blockMat_ee {A C : Matrix (Fin 2) (Fin 2) K} (i j : Fin 2) :
    blockMat A C (Sum.inl i) (Sum.inl j) = A i j := by
  simp [blockMat]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_blockMat_ef {A C : Matrix (Fin 2) (Fin 2) K} (i j : Fin 2) :
    blockMat A C (Sum.inl i) (Sum.inr j) = (A * C) i j := by
  simp [blockMat]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_blockMat_fe {A C : Matrix (Fin 2) (Fin 2) K} (i j : Fin 2) :
    blockMat A C (Sum.inr i) (Sum.inl j) = 0 := by
  simp [blockMat]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_blockMat_ff {A C : Matrix (Fin 2) (Fin 2) K} (i j : Fin 2) :
    blockMat A C (Sum.inr i) (Sum.inr j) = (A⁻¹ᵀ) i j := by
  simp [blockMat]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
theorem burnsideF48_spU_cent {ω : Kˣ} (hω1 : ω ≠ 1) (hω2 : (ω : K) ^ 2 ≠ 1)
    {q : StatedProj (StatedSp 2 K)} (hq : q ∈ projUnipotent 2 K)
    (hnq : (proj 2 K (burnsideF48_spNElt K))⁻¹ * q * proj 2 K (burnsideF48_spNElt K) ∈
      projUnipotent 2 K)
    (hc : proj 2 K (burnsideF48_spHElt ω 1) * q * (proj 2 K (burnsideF48_spHElt ω 1))⁻¹ = q) :
    q = 1 := by
  obtain ⟨Q, hQ, rfl⟩ := hq
  obtain ⟨R, hR, hRQ⟩ := hnq
  obtain ⟨A, C, hA, hC, hQmat⟩ := mem_unipotent.1 hQ
  obtain ⟨A', C', hA', hC', hRmat⟩ := mem_unipotent.1 hR
  set n := burnsideF48_spNElt K with hn
  set H := burnsideF48_spHElt ω 1 with hH
  have hC11 : C 1 1 = 0 := by
    have hRQ' : proj 2 K R = proj 2 K (n⁻¹ * Q * n) := by
      rw [hRQ]
      simp [map_mul, map_inv]
    obtain ⟨c, hc'⟩ := burnsideF48_sp_proj_eq_mat hRQ'
    have hmat : ((Q : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((n : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((n : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (((R : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
      have h1 : Q * n = n * (n⁻¹ * Q * n) := by group
      have h2 := congrArg (fun X : StatedSp 2 K => ((X : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1
      simp only [Subgroup.coe_mul, Units.val_mul] at h2 hc'
      rw [h2, hc']
    have e1 := congrFun (congrFun hmat (Sum.inl 1)) (Sum.inl 1)
    have e2 := congrFun (congrFun hmat (Sum.inr 1)) (Sum.inl 1)
    have hN : ((n : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      burnsideF48_spN K := rfl
    rw [hN, hQmat, hRmat] at e1 e2
    simp [burnsideF48_spN, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      burnsideF48_blockMat_ee, burnsideF48_blockMat_ef, burnsideF48_blockMat_fe,
      burnsideF48_blockMat_ff] at e1 e2
    have h1 : A 1 1 = 1 := hA.2 1
    have h2 : A 1 0 = 0 := hA.1 (by decide)
    have h3 : A' 1 1 = 1 := hA'.2 1
    have h4 : A⁻¹ 1 1 = 1 := hA.inv.2 1
    rw [h1, h2, h3] at e1
    rw [h4, h3] at e2
    linear_combination e1 - e2
  have hc1 : proj 2 K (H * Q) = proj 2 K (Q * H) := by
    rw [map_mul, map_mul]
    exact mul_inv_eq_iff_eq_mul.1 hc
  obtain ⟨c, hc'⟩ := burnsideF48_sp_proj_eq_mat hc1
  simp only [Subgroup.coe_mul, Units.val_mul] at hc'
  have hH' : ((H : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
    burnsideF48_spH (ω : K) 1 := by
    simp [hH, burnsideF48_spHElt, burnsideF48_spElt]
  rw [hH', hQmat] at hc'
  have e00 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inl 0)
  have e01 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inl 1)
  have e0f1 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inr 1)
  have e0f0 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inr 0)
  simp [burnsideF48_spH, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    burnsideF48_blockMat_ee, burnsideF48_blockMat_ef, burnsideF48_blockMat_fe,
    burnsideF48_blockMat_ff, Matrix.diagonal_apply] at e00 e01 e0f1 e0f0
  have hω0 : (ω : K) ≠ 0 := ω.ne_zero
  have hω1' : (ω : K) ≠ 1 := fun h => hω1 (Units.ext h)
  have hA00 : A 0 0 = 1 := hA.2 0
  have hA11 : A 1 1 = 1 := hA.2 1
  have hA10 : A 1 0 = 0 := hA.1 (by decide)
  have hC10 : C 1 0 = C 0 1 := by
    have := congrFun (congrFun hC 0) 1
    simpa using this
  rw [hA00] at e00 e0f1 e0f0
  rw [hC10] at e0f0
  have hcc : c = 1 := by
    have h : (ω : K) * (c - 1) = 0 := by linear_combination (-1 : K) * e00
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hω0)
  subst hcc
  have hA01 : A 0 1 = 0 := by
    have h : A 0 1 * (1 - (ω : K)) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hω1'.symm)
  rw [hA01, hC11] at e0f1
  rw [hA01] at e0f0
  have hC01 : C 0 1 = 0 := by
    have h : C 0 1 * (1 - (ω : K)) = 0 := by linear_combination e0f1
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hω1'.symm)
  have hC00 : C 0 0 = 0 := by
    have h : C 0 0 * (1 - (ω : K) ^ 2) = 0 := by
      field_simp at e0f0
      linear_combination e0f0
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hω2.symm)
  have hA1 : A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA00, hA01, hA10, hA11]
  have hC0 : C = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC00, hC01, hC10, hC11]
  have hQ1 : Q = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hQmat, hA1, hC0, blockMat_one]
    rfl
  rw [hQ1, map_one]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem burnsideF48_sp_proj_mem_projStabilizer (W : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (x : StatedSp 2 K) : proj 2 K x ∈ projStabilizer 2 K W ↔ x ∈ stabilizer 2 K W := by
  rw [← comap_projStabilizer W]
  rfl

theorem burnsideF48_exists_unit_sq_ne_one [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ ω : Kˣ, ω ≠ 1 ∧ (ω : K) ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  have hcon' : ∀ ω : Kˣ, ω ≠ 1 → (ω : K) ^ 2 = 1 := fun ω hω => by
    by_contra h
    exact hcon ⟨ω, hω, h⟩
  have hall : ∀ x : K, x = 0 ∨ x = 1 ∨ x = -1 := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl hx
    · by_cases hx1 : (Units.mk0 x hx) = 1
      · exact Or.inr (Or.inl (by simpa using congrArg Units.val hx1))
      · have h2 := hcon' _ hx1
        have : x * x = 1 := by simpa [sq] using h2
        rcases mul_self_eq_one_iff.1 this with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  have hfin : Nat.card K ≤ 3 := by
    have := Fintype.ofFinite K
    have h3 : (Finset.univ : Finset K) ⊆ {0, 1, -1} := fun x _ => by
      simpa using hall x
    calc Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
      _ = (Finset.univ : Finset K).card := (Finset.card_univ).symm
      _ ≤ ({0, 1, -1} : Finset K).card := Finset.card_le_card h3
      _ ≤ 3 := Finset.card_le_three
  omega

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem burnsideF48_Sp4_cartan_proj [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ n w h : StatedProj (StatedSp 2 K),
      n ∈ projStabilizer 2 K (flag 2 K 1) ∧ n ∉ projStabilizer 2 K (flag 2 K 2) ∧
      h ∈ projStabilizer 2 K (flag 2 K 1) ∧ h ∈ projStabilizer 2 K (flag 2 K 2) ∧
      n⁻¹ * h * n ∈ projStabilizer 2 K (flag 2 K 2) ∧
      w⁻¹ * h * w ∈ projStabilizer 2 K (flag 2 K 1) ∧
      (¬ ∃ k ∈ projStabilizer 2 K (flag 2 K 1), ∃ l ∈ projStabilizer 2 K (flag 2 K 2),
        ∃ k' ∈ projStabilizer 2 K (flag 2 K 1), w = k * l * k') ∧
      ∀ q ∈ projUnipotent 2 K, n⁻¹ * q * n ∈ projUnipotent 2 K → h * q * h⁻¹ = q → q = 1 := by
  obtain ⟨ω, hω1, hω2⟩ := burnsideF48_exists_unit_sq_ne_one hK
  have hHN : burnsideF48_spHElt ω 1 * burnsideF48_spNElt K =
      burnsideF48_spNElt K * burnsideF48_spHElt ω 1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    change burnsideF48_spH (ω : K) ((1 : Kˣ) : K) * burnsideF48_spN K =
      burnsideF48_spN K * burnsideF48_spH (ω : K) ((1 : Kˣ) : K)
    rw [Units.val_one]
    exact burnsideF48_spH_mul_spN ω.ne_zero
  have hHW : burnsideF48_spHElt ω 1 * burnsideF48_spWElt K =
      burnsideF48_spWElt K * burnsideF48_spHElt ω⁻¹ 1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    change burnsideF48_spH (ω : K) ((1 : Kˣ) : K) * burnsideF48_spW K =
      burnsideF48_spW K * burnsideF48_spH ((ω⁻¹ : Kˣ) : K) ((1 : Kˣ) : K)
    rw [Units.val_one, Units.val_inv_eq_inv_val]
    have := burnsideF48_spH_mul_spW (K := K) (ω : K) 1
    rwa [inv_one] at this
  refine ⟨proj 2 K (burnsideF48_spNElt K), proj 2 K (burnsideF48_spWElt K),
    proj 2 K (burnsideF48_spHElt ω 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [burnsideF48_sp_proj_mem_projStabilizer]
    exact burnsideF48_spNElt_mem_stab_one
  · rw [burnsideF48_sp_proj_mem_projStabilizer]
    exact burnsideF48_spNElt_not_mem_stab_two
  · rw [burnsideF48_sp_proj_mem_projStabilizer]
    exact burnsideF48_spHElt_mem_stab ω 1 (by norm_num)
  · rw [burnsideF48_sp_proj_mem_projStabilizer]
    exact burnsideF48_spHElt_mem_stab ω 1 (by norm_num)
  · rw [← map_inv, ← map_mul, ← map_mul, burnsideF48_sp_proj_mem_projStabilizer]
    have h2 : (burnsideF48_spNElt K)⁻¹ * burnsideF48_spHElt ω 1 * burnsideF48_spNElt K =
        burnsideF48_spHElt ω 1 := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]
      exact hHN
    rw [h2]
    exact burnsideF48_spHElt_mem_stab ω 1 (by norm_num)
  · rw [← map_inv, ← map_mul, ← map_mul, burnsideF48_sp_proj_mem_projStabilizer]
    have h2 : (burnsideF48_spWElt K)⁻¹ * burnsideF48_spHElt ω 1 * burnsideF48_spWElt K =
        burnsideF48_spHElt ω⁻¹ 1 := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]
      exact hHW
    rw [h2]
    exact burnsideF48_spHElt_mem_stab ω⁻¹ 1 (by norm_num)
  · rintro ⟨k, ⟨k₀, hk₀, rfl⟩, l, ⟨l₀, hl₀, rfl⟩, k', ⟨k₀', hk₀', rfl⟩, hkl⟩
    have h1 : proj 2 K (k₀ * l₀ * k₀') = proj 2 K (burnsideF48_spWElt K) := by
      rw [map_mul, map_mul]
      exact hkl.symm
    have hz : (k₀ * l₀ * k₀')⁻¹ * burnsideF48_spWElt K ∈ spScalars 2 K := QuotientGroup.eq.1 h1
    have hz' := spScalars_le_stabilizer (flag 2 K 1) hz
    refine burnsideF48_spWElt_ne_mul hk₀ hl₀
      ((stabilizer 2 K (flag 2 K 1)).mul_mem hk₀' hz') ?_
    group
  · intro q hq hnq hc
    exact burnsideF48_spU_cent hω1 hω2 hq hnq hc

end Sp4Core

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
noncomputable def burnsideF48_spIso {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .Sp4 p f H) :
    StatedProj (StatedSp 2 marking.field) ≃* H :=
  marking.identification

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix in
private theorem burnsideF48_sp_keym {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .Sp4 p f H) (b : Bool) (x : StatedSp 2 marking.field) :
    x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (p ^ f) marking.field marking.basis b ↔
      x ∈ stabilizer 2 marking.field (flag 2 marking.field (if b then 2 else 1)) := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  rw [hbasis]
  have h1 : x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (p ^ f) marking.field 1 b ↔
      (x : GL (ChF.ClassicalRoots.Coord .Sp4) marking.field) ∈ ChF.ClassicalRoots.rawStabilizer
        ((fun vector => ((1 : GL (ChF.ClassicalRoots.Coord .Sp4) marking.field) :
          Matrix (ChF.ClassicalRoots.Coord .Sp4) (ChF.ClassicalRoots.Coord .Sp4)
            marking.field).mulVec vector) ''
          ChF.ClassicalRoots.coordinateSpace (if b then ChF.ClassicalRoots.flagTwo .Sp4
            else ChF.ClassicalRoots.flagOne .Sp4)) :=
    Iff.rfl
  rw [h1, burnsideF4h_cl_mem_rawStabilizer, mem_stabilizer,
    burnsideF4h_cl_map_eq_iff _
      (C := (((x⁻¹ : StatedSp 2 marking.field) : GL (Fin 2 ⊕ Fin 2) marking.field) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field))
      (by rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
        Units.val_one])
      (by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one])]
  simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
  cases b
  · simp only [Bool.false_eq_true, if_false, ChF.ClassicalRoots.flagOne]
    exact forall_congr' fun v => by
      rw [(burnsideF4h_cl_sp_coordinateSpace _).1, (burnsideF4h_cl_sp_coordinateSpace _).1]
  · simp only [if_true, ChF.ClassicalRoots.flagTwo]
    exact forall_congr' fun v => by
      rw [(burnsideF4h_cl_sp_coordinateSpace _).2, (burnsideF4h_cl_sp_coordinateSpace _).2]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem burnsideF48_sp_parabolic_eq {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .Sp4 p f H) (b : Bool) :
    marking.parabolic b = (projStabilizer 2 marking.field
      (flag 2 marking.field (if b then 2 else 1))).map (burnsideF48_spIso marking).toMonoidHom := by
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨proj 2 marking.field x, ⟨x, (burnsideF48_sp_keym marking b x).1 hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, (burnsideF48_sp_keym marking b x).2 hx, rfl⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem burnsideF48_spIso_mem_iff {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .Sp4 p f H) (b : Bool)
    (g : StatedProj (StatedSp 2 marking.field)) :
    burnsideF48_spIso marking g ∈ marking.parabolic b ↔
      g ∈ projStabilizer 2 marking.field (flag 2 marking.field (if b then 2 else 1)) := by
  rw [burnsideF48_sp_parabolic_eq marking b, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Quasithin
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_Sp4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .Sp4 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ ChF.GLKind.Sp4.m)
    (hq : 4 ≤ p ^ f) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 4) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨marking, h1, h2⟩ := burnsideF48_marking (c := .Sp4) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = p ^ f := by simpa using marking.field_card
  haveI : CharP marking.field p := by
    have := Fintype.ofFinite marking.field
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨n, w, h, hn1, hn2, hh1, hh2, hh3, hh4, hw, hQ⟩ :=
    burnsideF48_Sp4_cartan_proj (K := marking.field) (by rw [hK]; exact hq)
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnipotent (K := marking.field) p (r := 2) (by norm_num)
  refine burnsideF48_cartanFPF_of_data_four hyp hp hm rfl hpoly (burnsideF48_spIso marking)
    (projStabilizer 2 marking.field (flag 2 marking.field 1))
    (projStabilizer 2 marking.field (flag 2 marking.field 2))
    (projUnipotent 2 marking.field) ?_ ?_ (burnsideF48_isSylowOf_of_equiv _ ⟨SU, hSU⟩) ?_
    n w h hn1 hn2 hh1 hh2 hh3 hh4 hw hQ
  · intro g
    have := burnsideF48_spIso_mem_iff marking false g
    simp only [Bool.false_eq_true, if_false] at this
    rw [← this, ← h1]
    exact Subgroup.mem_subgroupOf.symm
  · intro g
    have := burnsideF48_spIso_mem_iff marking true g
    simp only [if_true] at this
    rw [← this, ← h2]
    exact Subgroup.mem_subgroupOf.symm
  · exact Subgroup.map_mono (fun x hx => (mem_borelSubgroup.1 (unipotent_le_borelSubgroup hx)) 1
      le_rfl (by norm_num))

theorem burnsideF48_simple_Sp4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .Sp4 p f Gp M₁ M₂) (hq : 4 ≤ p ^ f) : IsSimpleGroup ↥Gp := by
  obtain ⟨-, -, K, hK, hKfin, hcard, ⟨e⟩⟩ := hyp.model
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hcard]; exact hq)))
  exact e.isSimpleGroup

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_Sp4 (hF : F_4_5) (hcompat : ChF.NativeChartCompatibilityGoal)
    {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .Sp4 p f Gp M₁ M₂) (hq : 4 ≤ p ^ f) : ChF.F48Concl .Sp4 p f Gp M₁ M₂ := by
  have hP := burnsideF48_parabolics_of_compat hcompat hyp
  have hp := ChF.burnsideF4a_prime_of_isGenLie hyp.model
  have hm := burnsideF48_three_le_m .Sp4
  have hL : ChF.GLKind.Sp4.IsLie :=
    show ChF.GLKind.Sp4 ≠ ChF.GLKind.G2d ∧ ChF.GLKind.Sp4 ≠ ChF.GLKind.Tits from
      ⟨by decide, by decide⟩
  refine burnsideF48_concl_of_F45_cartan hF hyp hL (burnsideF48_simple_Sp4 hyp hq) hP ?_
  exact burnsideF48_cartanFPF_Sp4 hyp hp hm hq
    (burnsideF48_facts45L_of_F45 hF hyp hL hp hm hP).poly

end CFSG.ASVolI
