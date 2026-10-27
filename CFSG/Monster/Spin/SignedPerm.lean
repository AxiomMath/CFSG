module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Monster.Spin

open Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem zmod2_add_self : ∀ c : ZMod 2, c + c = 0 := by decide

variable (R : Type*) [CommRing R]

@[expose] def sgnR (t : ZMod 2) : R := if t = 0 then 1 else -1

variable {R}

@[simp] theorem sgnR_zero : sgnR R 0 = 1 := rfl

@[simp] theorem sgnR_one : sgnR R 1 = -1 := rfl

theorem sgnR_add (s t : ZMod 2) : sgnR R (s + t) = sgnR R s * sgnR R t := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
  · simp
  · simp
  · simp
  · rw [zmod2_add_self, sgnR_zero, sgnR_one, neg_mul_neg, mul_one]

theorem sgnR_mul_self (t : ZMod 2) : sgnR R t * sgnR R t = 1 := by
  rw [← sgnR_add, zmod2_add_self, sgnR_zero]

theorem sgnR_ne_zero [Nontrivial R] (t : ZMod 2) : sgnR R t ≠ 0 := by
  intro h
  have := sgnR_mul_self (R := R) t
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem sgnR_injective (h2 : (2 : R) ≠ 0) : Function.Injective (sgnR R) := by
  have h : (1 : R) ≠ -1 := by
    intro h
    apply h2
    calc (2 : R) = 1 + 1 := one_add_one_eq_two.symm
      _ = -1 + 1 := by rw [← h]
      _ = 0 := neg_add_cancel 1
  intro s t hst
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
  · rfl
  · exact absurd hst h
  · exact absurd hst.symm h
  · rfl

theorem sgnR_eq_one_iff (h2 : (2 : R) ≠ 0) (t : ZMod 2) : sgnR R t = 1 ↔ t = 0 :=
  ⟨fun h => sgnR_injective h2 (h.trans sgnR_zero.symm), fun h => h ▸ sgnR_zero⟩

theorem map_sgnR {S : Type*} [CommRing S] (f : R →+* S) (t : ZMod 2) :
    f (sgnR R t) = sgnR S t := by
  rcases zmod2_cases t with rfl | rfl
  · simp
  · simp

theorem sgnR_add_one (t : ZMod 2) : sgnR R (t + 1) = -sgnR R t := by
  rw [sgnR_add, sgnR_one, mul_neg_one]

theorem sum_sgnR_add (c : ZMod 2) : ∑ t : ZMod 2, sgnR R (t + c) = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide),
    zero_add, add_comm (1 : ZMod 2) c, sgnR_add_one, add_neg_cancel]

variable {ι : Type*} [DecidableEq ι]

variable (R) in
@[expose] def spm (σ : ι → ι) (ε : ι → ZMod 2) : Matrix ι ι R :=
  Matrix.of fun i j => if j = σ i then sgnR R (ε i) else 0

theorem spm_apply (σ : ι → ι) (ε : ι → ZMod 2) (i j : ι) :
    spm R σ ε i j = if j = σ i then sgnR R (ε i) else 0 := rfl

theorem spm_apply_mem (σ : ι → ι) (ε : ι → ZMod 2) (i j : ι) :
    spm R σ ε i j = 0 ∨ spm R σ ε i j = 1 ∨ spm R σ ε i j = -1 := by
  rw [spm_apply]
  split_ifs
  · rcases zmod2_cases (ε i) with h | h <;> rw [h] <;> simp
  · exact Or.inl rfl

theorem map_spm {S : Type*} [CommRing S] (f : R →+* S) (σ : ι → ι) (ε : ι → ZMod 2) :
    (spm R σ ε).map f = spm S σ ε := by
  ext i j
  simp only [Matrix.map_apply, spm_apply]
  split_ifs
  · exact map_sgnR f _
  · exact map_zero f

theorem spm_row (σ : ι → ι) (ε : ι → ZMod 2) (i : ι) :
    (spm R σ ε).row i = sgnR R (ε i) • Pi.single (σ i) 1 := by
  ext j
  simp only [row_apply, spm_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

theorem spm_id_zero : spm R (fun i : ι => i) (fun _ => 0) = 1 := by
  ext i j
  simp only [spm_apply, sgnR_zero, one_apply, eq_comm]

theorem spm_congr {σ σ' : ι → ι} {ε ε' : ι → ZMod 2} (hσ : ∀ i, σ i = σ' i)
    (hε : ∀ i, ε i = ε' i) : spm R σ ε = spm R σ' ε' := by
  rw [funext hσ, funext hε]

theorem spm_eq_one {σ : ι → ι} {ε : ι → ZMod 2} (hσ : ∀ i, σ i = i) (hε : ∀ i, ε i = 0) :
    spm R σ ε = 1 :=
  (spm_congr hσ hε).trans spm_id_zero

theorem sgnR_smul_spm (s : ZMod 2) (σ : ι → ι) (ε : ι → ZMod 2) :
    sgnR R s • spm R σ ε = spm R σ (fun i => s + ε i) := by
  ext i j
  simp only [smul_apply, spm_apply, smul_eq_mul, mul_ite, mul_zero, sgnR_add]

theorem neg_spm (σ : ι → ι) (ε : ι → ZMod 2) : -spm R σ ε = spm R σ (fun i => 1 + ε i) := by
  rw [← sgnR_smul_spm, sgnR_one, neg_one_smul]

theorem spm_transpose_of_involutive {σ : ι → ι} (hσ : Function.Involutive σ)
    (ε : ι → ZMod 2) : (spm R σ ε)ᵀ = spm R σ (fun i => ε (σ i)) := by
  ext i j
  simp only [transpose_apply, spm_apply]
  by_cases h : j = σ i
  · subst h
    rw [ite_eq_left (hσ i).symm, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right]
    rintro rfl
    exact h (hσ j).symm

theorem spm_injective [Nontrivial R] (h2 : (2 : R) ≠ 0) {σ σ' : ι → ι} {ε ε' : ι → ZMod 2}
    (h : spm R σ ε = spm R σ' ε') : σ = σ' ∧ ε = ε' := by
  have hσ : ∀ i, σ i = σ' i := by
    intro i
    have := congrFun (congrFun h i) (σ i)
    rw [spm_apply, spm_apply, ite_eq_left rfl] at this
    by_contra hne
    rw [ite_eq_right hne] at this
    exact sgnR_ne_zero _ this
  refine ⟨funext hσ, funext fun i => ?_⟩
  have := congrFun (congrFun h i) (σ i)
  rw [spm_apply, spm_apply, ite_eq_left rfl, ite_eq_left (hσ i)] at this
  exact sgnR_injective h2 this

variable [Fintype ι]

theorem single_vecMul_spm (σ : ι → ι) (ε : ι → ZMod 2) (i : ι) :
    Pi.single i 1 ᵥ* spm R σ ε = sgnR R (ε i) • Pi.single (σ i) 1 := by
  rw [single_one_vecMul, spm_row]

theorem vecMul_spm_apply (σ : ι → ι) (ε : ι → ZMod 2) (v : ι → R) (j : ι) :
    (v ᵥ* spm R σ ε) j = ∑ i, if σ i = j then v i * sgnR R (ε i) else 0 := by
  simp only [vecMul, dotProduct, spm_apply, mul_ite, mul_zero, eq_comm]

theorem spm_mul_apply (σ : ι → ι) (ε : ι → ZMod 2) (M : Matrix ι ι R) (i j : ι) :
    (spm R σ ε * M) i j = sgnR R (ε i) * M (σ i) j := by
  simp only [mul_apply, spm_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem spm_mul_spm (σ τ : ι → ι) (ε φ : ι → ZMod 2) :
    spm R σ ε * spm R τ φ = spm R (τ ∘ σ) (fun i => ε i + φ (σ i)) := by
  ext i j
  rw [spm_mul_apply, spm_apply, spm_apply, sgnR_add, Function.comp_apply, mul_ite, mul_zero]

theorem spm_transpose_mul_self {σ : ι → ι} (hσ : Function.Involutive σ) (ε : ι → ZMod 2) :
    (spm R σ ε)ᵀ * spm R σ ε = 1 := by
  rw [spm_transpose_of_involutive hσ, spm_mul_spm]
  exact spm_eq_one (fun i => hσ i) (fun i => zmod2_add_self _)

theorem spm_mul_transpose_self {σ : ι → ι} (hσ : Function.Involutive σ) (ε : ι → ZMod 2) :
    spm R σ ε * (spm R σ ε)ᵀ = 1 := by
  rw [spm_transpose_of_involutive hσ, spm_mul_spm]
  refine spm_eq_one (fun i => hσ i) (fun i => ?_)
  simp only [hσ i, zmod2_add_self]

theorem trace_spm (σ : ι → ι) (ε : ι → ZMod 2) :
    trace (spm R σ ε) = ∑ i, if σ i = i then sgnR R (ε i) else 0 := by
  simp only [trace, diag_apply, spm_apply, eq_comm]

end CFSG.Monster.Spin
