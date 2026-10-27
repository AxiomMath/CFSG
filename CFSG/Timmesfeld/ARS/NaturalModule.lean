module

public import CFSG.Timmesfeld.RankOne.SL2
public import Mathlib.Algebra.CharP.Pi

public section

namespace CFSG.Timmesfeld.ARS.NaturalModule

open Matrix CFSG.Timmesfeld.RankOne

variable (K : Type*) [Field K]

@[expose] def weylElt [CharP K 2] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

variable {K}

@[expose] def diagElt (c : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩

theorem coe_weylElt [CharP K 2] :
    ((weylElt K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; 1, 0] := rfl

theorem coe_diagElt (c : Kˣ) :
    ((diagElt c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] := rfl

theorem coe_upperElt (t : K) :
    ((upperElt K t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, t; 0, 1] := rfl

theorem coe_lowerElt (t : K) :
    ((lowerElt K t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 0; t, 1] := rfl

theorem diagElt_mul_diagElt (c d : Kˣ) : diagElt c * diagElt d = diagElt (c * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagElt, mul_comm]

theorem diagElt_one : diagElt (1 : Kˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagElt]

theorem diagElt_mul_upperElt (c : Kˣ) (t : K) :
    diagElt c * upperElt K t = upperElt K ((c : K) ^ 2 * t) * diagElt c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagElt, coe_upperElt]
  field_simp

theorem upperElt_mul_diagElt (c : Kˣ) (t : K) :
    upperElt K t * diagElt c = diagElt c * upperElt K (((c⁻¹ : Kˣ) : K) ^ 2 * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagElt, coe_upperElt]
  field_simp

theorem diagElt_mul_lowerElt (c : Kˣ) (t : K) :
    diagElt c * lowerElt K t = lowerElt K (((c⁻¹ : Kˣ) : K) ^ 2 * t) * diagElt c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagElt, coe_lowerElt]
  field_simp

theorem upperUnipotent_sup_lowerUnipotent : upperUnipotent K ⊔ lowerUnipotent K = ⊤ := by
  have hU : ∀ t, upperElt K t ∈ upperUnipotent K ⊔ lowerUnipotent K :=
    fun t => Subgroup.mem_sup_left ((mem_upperUnipotent_iff K).2 ⟨t, rfl⟩)
  have hL : ∀ t, lowerElt K t ∈ upperUnipotent K ⊔ lowerUnipotent K :=
    fun t => Subgroup.mem_sup_right ((mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩)
  have hne : ∀ M : SpecialLinearGroup (Fin 2) K, (M : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 →
      M ∈ upperUnipotent K ⊔ lowerUnipotent K := by
    intro M hc
    have hdet := M.2
    rw [det_fin_two] at hdet
    have hM : M = upperElt K (((M : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) /
        (M : Matrix (Fin 2) (Fin 2) K) 1 0) * lowerElt K ((M : Matrix (Fin 2) (Fin 2) K) 1 0) *
        upperElt K (((M : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) /
        (M : Matrix (Fin 2) (Fin 2) K) 1 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coe_upperElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> first | ring1 | linear_combination hdet | linear_combination -hdet
    rw [hM]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  refine eq_top_iff.2 fun M _ => ?_
  by_cases hc : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hdet := M.2
    rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
    have ha : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have h1 : lowerElt K 1 * M ∈ upperUnipotent K ⊔ lowerUnipotent K := hne _ (by
      simpa [coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha)
    have h2 : M = (lowerElt K 1)⁻¹ * (lowerElt K 1 * M) := by group
    rw [h2]
    exact mul_mem (inv_mem (hL 1)) h1
  · exact hne M hc

theorem sl2_induction {P : SpecialLinearGroup (Fin 2) K → Prop} (one : P 1)
    (mul : ∀ x y, P x → P y → P (x * y)) (inv : ∀ x, P x → P x⁻¹)
    (upper : ∀ t, P (upperElt K t)) (lower : ∀ t, P (lowerElt K t))
    (x : SpecialLinearGroup (Fin 2) K) : P x := by
  let S : Subgroup (SpecialLinearGroup (Fin 2) K) :=
    { carrier := {x | P x}
      mul_mem' := fun {x y} hx hy => mul x y hx hy
      one_mem' := one
      inv_mem' := fun {x} hx => inv x hx }
  have hU : upperUnipotent K ≤ S := fun g hg => by
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 hg
    exact upper t
  have hL : lowerUnipotent K ≤ S := fun g hg => by
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff K).1 hg
    exact lower t
  have hx : x ∈ upperUnipotent K ⊔ lowerUnipotent K := by
    rw [upperUnipotent_sup_lowerUnipotent]
    exact Subgroup.mem_top x
  exact sup_le hU hL hx

theorem exists_mulVec_eq {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h0]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem vec2_zero : (![0, 0] : Fin 2 → K) = 0 := by
  ext i
  fin_cases i <;> rfl

theorem upperElt_mulVec (t : K) (v : Fin 2 → K) :
    (upperElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0 + t * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [coe_upperElt, mulVec, dotProduct, Fin.sum_univ_two]

theorem upperElt_mulVec_sub (t : K) (v : Fin 2 → K) :
    (upperElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v = ![t * v 1, 0] := by
  rw [upperElt_mulVec]
  ext i
  fin_cases i <;> simp

theorem lowerElt_mulVec (t : K) (v : Fin 2 → K) :
    (lowerElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0, t * v 0 + v 1] := by
  ext i
  fin_cases i <;> simp [coe_lowerElt, mulVec, dotProduct, Fin.sum_univ_two]

theorem diagElt_mulVec (c : Kˣ) (v : Fin 2 → K) :
    (diagElt c : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![(c : K) * v 0, ((c⁻¹ : Kˣ) : K) * v 1] := by
  ext i
  fin_cases i <;> simp [coe_diagElt, mulVec, dotProduct, Fin.sum_univ_two]

theorem diagElt_inv (c : Kˣ) : (diagElt c)⁻¹ = diagElt c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagElt_mul_diagElt, mul_inv_cancel, diagElt_one]

theorem forall_upperElt_mulVec_eq_iff (v : Fin 2 → K) :
    (∀ t : K, (upperElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) ↔ v 1 = 0 := by
  constructor
  · intro h
    have := congrFun (h 1) 0
    rw [upperElt_mulVec] at this
    simpa using this
  · intro h t
    rw [upperElt_mulVec]
    ext i
    fin_cases i <;> simp [h]

theorem forall_lowerElt_mulVec_eq_iff (v : Fin 2 → K) :
    (∀ t : K, (lowerElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) ↔ v 0 = 0 := by
  constructor
  · intro h
    have := congrFun (h 1) 1
    rw [lowerElt_mulVec] at this
    simpa using this
  · intro h t
    rw [lowerElt_mulVec]
    ext i
    fin_cases i <;> simp [h]

theorem diagElt_mem_normalizer_upperUnipotent (c : Kˣ) :
    diagElt c ∈ Subgroup.normalizer (upperUnipotent K : Set (SpecialLinearGroup (Fin 2) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 hg
    rw [diagElt_mul_upperElt, mul_assoc, mul_inv_cancel, mul_one]
    exact (mem_upperUnipotent_iff K).2 ⟨_, rfl⟩
  · intro hg
    obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff K).1 hg
    have : g = (diagElt c)⁻¹ * upperElt K t * diagElt c := by rw [← ht]; group
    rw [this, diagElt_inv, diagElt_mul_upperElt, mul_assoc, ← diagElt_inv, inv_mul_cancel,
      mul_one]
    exact (mem_upperUnipotent_iff K).2 ⟨_, rfl⟩

theorem diagElt_mem_normalizer_lowerUnipotent (c : Kˣ) :
    diagElt c ∈ Subgroup.normalizer (lowerUnipotent K : Set (SpecialLinearGroup (Fin 2) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff K).1 hg
    rw [diagElt_mul_lowerElt, mul_assoc, mul_inv_cancel, mul_one]
    exact (mem_lowerUnipotent_iff K).2 ⟨_, rfl⟩
  · intro hg
    obtain ⟨t, ht⟩ := (mem_lowerUnipotent_iff K).1 hg
    have : g = (diagElt c)⁻¹ * lowerElt K t * diagElt c := by rw [← ht]; group
    rw [this, diagElt_inv, diagElt_mul_lowerElt, mul_assoc, ← diagElt_inv, inv_mul_cancel,
      mul_one]
    exact (mem_lowerUnipotent_iff K).2 ⟨_, rfl⟩

theorem eq_one_of_forall_mulVec_eq {g : SpecialLinearGroup (Fin 2) K}
    (h : ∀ v : Fin 2 → K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) : g = 1 := by
  have h0 := h ![1, 0]
  have h1 := h ![0, 1]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h0 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h0 1
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 1

variable [CharP K 2]

theorem weylElt_mul_self : weylElt K * weylElt K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_weylElt]

theorem upperElt_mul_self (t : K) : upperElt K t * upperElt K t = 1 := by
  rw [upperElt_mul, CharTwo.add_self_eq_zero, upperElt_zero]

theorem weylElt_mul_upperElt_mul_weylElt (t : K) :
    weylElt K * upperElt K t * weylElt K = lowerElt K t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_weylElt, coe_upperElt, coe_lowerElt]

theorem upperElt_one_mul_lowerElt_one_mul_upperElt_one :
    upperElt K 1 * lowerElt K 1 * upperElt K 1 = weylElt K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylElt, coe_upperElt, coe_lowerElt, CharTwo.add_self_eq_zero]

theorem weylElt_mul_diagElt (c : Kˣ) : weylElt K * diagElt c = diagElt c⁻¹ * weylElt K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_weylElt, coe_diagElt]

variable {V : Type*} [AddCommGroup V] [DistribMulAction (SpecialLinearGroup (Fin 2) K) V]

theorem weylElt_smul_weylElt_smul (v : V) : weylElt K • weylElt K • v = v := by
  rw [← mul_smul, weylElt_mul_self, one_smul]

theorem upperElt_smul_upperElt_smul (t : K) (v : V) : upperElt K t • upperElt K t • v = v := by
  rw [← mul_smul, upperElt_mul_self, one_smul]

theorem lowerElt_smul (t : K) (v : V) :
    lowerElt K t • v = weylElt K • upperElt K t • weylElt K • v := by
  rw [← weylElt_mul_upperElt_mul_weylElt, mul_smul, mul_smul]

@[expose] def natVec (w : V) (t : K) : V := upperElt K t • weylElt K • w - weylElt K • w

@[expose] def natMap (w : V) (v : Fin 2 → K) : V :=
  natVec w (v 0) + weylElt K • natVec w (v 1)

theorem natVec_zero (w : V) : natVec w (0 : K) = 0 := by
  simp [natVec, upperElt_zero]

theorem natMap_weylElt (w : V) (v : Fin 2 → K) :
    natMap w ((weylElt K : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = weylElt K • natMap w v := by
  have hv : (weylElt K : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 1, v 0] := by
    ext i
    fin_cases i <;> simp [coe_weylElt, mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv]
  simp only [natMap, Matrix.cons_val_zero, Matrix.cons_val_one, smul_add,
    weylElt_smul_weylElt_smul]
  abel

section Quadratic

variable (hquad : ∀ (s t : K) (v : V),
  upperElt K s • (upperElt K t • v - v) = upperElt K t • v - v)
include hquad

theorem upperElt_smul_natVec (w : V) (s t : K) : upperElt K s • natVec w t = natVec w t :=
  hquad s t _

theorem natVec_add (w : V) (s t : K) : natVec w (s + t) = natVec w s + natVec w t := by
  have h := hquad s t (weylElt K • w)
  have h' : upperElt K s • upperElt K t • weylElt K • w =
      (upperElt K t • weylElt K • w - weylElt K • w) + upperElt K s • weylElt K • w := by
    rw [← h, ← smul_add, sub_add_cancel]
  simp only [natVec]
  rw [← upperElt_mul, mul_smul, h']
  abel

theorem natMap_add (w : V) (v v' : Fin 2 → K) :
    natMap w (v + v') = natMap w v + natMap w v' := by
  simp only [natMap, Pi.add_apply, natVec_add hquad, smul_add]
  abel

variable (hfix : ∀ v : V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0)
include hfix

theorem natVec_one {w : V} (hw : ∀ t : K, upperElt K t • w = w) : natVec w (1 : K) = w := by
  have hul : upperElt K 1 • weylElt K • w = lowerElt K 1 • w := by
    rw [← upperElt_one_mul_lowerElt_one_mul_upperElt_one, mul_smul, mul_smul, hw,
      upperElt_smul_upperElt_smul]
  have hy : lowerElt K 1 • w - w = weylElt K • natVec w (1 : K) := by
    rw [lowerElt_smul, natVec, smul_sub, weylElt_smul_weylElt_smul]
  have hz' : natVec w (1 : K) - w = weylElt K • natVec w (1 : K) - weylElt K • w := by
    rw [← hy, natVec, hul]
    abel
  refine sub_eq_zero.1 (hfix _ (sl2_induction (one_smul _ _) (fun x y hx hy => ?_)
    (fun x hx => ?_) (fun t => ?_) (fun t => ?_)))
  · rw [mul_smul, hy, hx]
  · rw [inv_smul_eq_iff, hx]
  · rw [smul_sub, upperElt_smul_natVec hquad, hw]
  · rw [hz', smul_sub, lowerElt_smul, lowerElt_smul, weylElt_smul_weylElt_smul,
      weylElt_smul_weylElt_smul, upperElt_smul_natVec hquad, hw]

theorem natVec_sq {w : V} (hw : ∀ t : K, upperElt K t • w = w) (c : Kˣ) :
    natVec w ((c : K) ^ 2) = diagElt c • diagElt c • w := by
  have hw' : ∀ t : K, upperElt K t • diagElt c • w = diagElt c • w := by
    intro t
    rw [← mul_smul, upperElt_mul_diagElt, mul_smul, hw]
  have h1 := natVec_one hquad hfix hw'
  have h2 : natVec (diagElt c • w) (1 : K) = diagElt c⁻¹ • natVec w ((c : K) ^ 2) := by
    have hu := upperElt_mul_diagElt c⁻¹ (1 : K)
    rw [inv_inv, mul_one] at hu
    simp only [natVec]
    rw [← mul_smul (weylElt K), weylElt_mul_diagElt, mul_smul, ← mul_smul (upperElt K 1), hu,
      mul_smul, smul_sub]
  rw [h2] at h1
  rw [← h1, ← mul_smul, diagElt_mul_diagElt, mul_inv_cancel, diagElt_one, one_smul]

variable [PerfectRing K 2]

theorem natVec_eq_diagElt_smul {w : V} (hw : ∀ t : K, upperElt K t • w = w) (c : Kˣ) :
    natVec w (c : K) = diagElt c • w := by
  obtain ⟨d, hd⟩ := surjective_frobenius K 2 (c : K)
  rw [frobenius_def] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hd
    exact c.ne_zero hd.symm
  have he : Units.mk0 d hd0 * Units.mk0 d hd0 = c := Units.ext (by simp [← hd, sq])
  have h := natVec_sq hquad hfix hw (Units.mk0 d hd0)
  rw [Units.val_mk0, hd] at h
  rw [h, ← mul_smul, diagElt_mul_diagElt, he]

theorem upperElt_smul_weylElt_smul_natVec {w : V} (hw : ∀ t : K, upperElt K t • w = w)
    (r t : K) :
    upperElt K r • weylElt K • natVec w t = natVec w (r * t) + weylElt K • natVec w t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [natVec_zero]
  rcases eq_or_ne r 0 with rfl | hr
  · simp [upperElt_zero, natVec_zero]
  set c := Units.mk0 t ht
  set d := Units.mk0 r hr
  have hu := upperElt_mul_diagElt c⁻¹ r
  rw [inv_inv] at hu
  have h1 : natVec w t = diagElt c • w := natVec_eq_diagElt_smul hquad hfix hw c
  have h2 : natVec w ((c : K) ^ 2 * r) = diagElt (c ^ 2 * d) • w := by
    rw [← natVec_eq_diagElt_smul hquad hfix hw]
    simp [c, d]
  have h3 : natVec w (r * t) = diagElt (c * d) • w := by
    rw [mul_comm r t, ← natVec_eq_diagElt_smul hquad hfix hw]
    simp [c, d]
  have hω : weylElt K • diagElt c • w = diagElt c⁻¹ • weylElt K • w := by
    rw [← mul_smul, weylElt_mul_diagElt, mul_smul]
  have h4 : upperElt K ((c : K) ^ 2 * r) • weylElt K • w =
      natVec w ((c : K) ^ 2 * r) + weylElt K • w := by
    rw [natVec, sub_add_cancel]
  rw [h1, hω, ← mul_smul, hu, mul_smul, h4, smul_add, h2, h3, ← mul_smul, diagElt_mul_diagElt]
  congr 3
  rw [pow_two]
  group

variable {w : V} (hw : ∀ t : K, upperElt K t • w = w)
include hw

theorem natMap_upperElt (r : K) (v : Fin 2 → K) :
    natMap w ((upperElt K r : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = upperElt K r • natMap w v := by
  have hv : (upperElt K r : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0 + r * v 1, v 1] := by
    ext i
    fin_cases i <;> simp [coe_upperElt, mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv]
  simp only [natMap, Matrix.cons_val_zero, Matrix.cons_val_one, smul_add,
    upperElt_smul_natVec hquad, upperElt_smul_weylElt_smul_natVec hquad hfix hw,
    natVec_add hquad]
  abel

theorem natMap_mulVec (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    natMap w ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • natMap w v := by
  have key : ∀ x : SpecialLinearGroup (Fin 2) K, ∀ v : Fin 2 → K,
      natMap w ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • natMap w v := by
    refine sl2_induction (fun v => by simp) (fun x y hx hy v => ?_) (fun x hx v => ?_)
      (natMap_upperElt hquad hfix hw) (fun t v => ?_)
    · change natMap w (((x : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K)) *ᵥ v) =
        (x * y) • natMap w v
      rw [← mulVec_mulVec, hx, hy, mul_smul]
    · rw [eq_inv_smul_iff, ← hx, mulVec_mulVec]
      change natMap w (((x * x⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        v) = natMap w v
      rw [mul_inv_cancel]
      change natMap w ((1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = natMap w v
      rw [one_mulVec]
    · rw [← weylElt_mul_upperElt_mul_weylElt]
      change natMap w (((weylElt K : Matrix (Fin 2) (Fin 2) K) * (upperElt K t : Matrix (Fin 2)
        (Fin 2) K) * (weylElt K : Matrix (Fin 2) (Fin 2) K)) *ᵥ v) = _
      rw [← mulVec_mulVec, ← mulVec_mulVec, natMap_weylElt, natMap_upperElt hquad hfix hw,
        natMap_weylElt, mul_smul, mul_smul]
  exact key x v

omit [PerfectRing K 2] in
theorem natMap_e₁ : natMap w (![1, 0] : Fin 2 → K) = w := by
  simp [natMap, natVec_one hquad hfix hw, natVec_zero]

end Quadratic

section Embedding

variable {θ : (Fin 2 → K) →+ V}
  (hθ : ∀ (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
    θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v)
include hθ

omit [CharP K 2] in
theorem upperElt_smul_sub_eq (t : K) (v : Fin 2 → K) :
    upperElt K t • θ v - θ v = θ ![t * v 1, 0] := by
  rw [← hθ, upperElt_mulVec, ← map_sub]
  congr 1
  ext i
  fin_cases i <;> simp

variable (hinj : Function.Injective θ)
include hinj

omit [CharP K 2] in
theorem forall_upper_smul_eq_iff (v : Fin 2 → K) :
    (∀ a ∈ upperUnipotent K, a • θ v = θ v) ↔ v 1 = 0 := by
  rw [← forall_upperElt_mulVec_eq_iff]
  constructor
  · intro h t
    exact hinj (by rw [hθ, h _ ((mem_upperUnipotent_iff K).2 ⟨t, rfl⟩)])
  · intro h a ha
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 ha
    rw [← hθ, h t]

omit [CharP K 2] in
theorem forall_lower_smul_eq_iff (v : Fin 2 → K) :
    (∀ b ∈ lowerUnipotent K, b • θ v = θ v) ↔ v 0 = 0 := by
  rw [← forall_lowerElt_mulVec_eq_iff]
  constructor
  · intro h t
    exact hinj (by rw [hθ, h _ ((mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩)])
  · intro h b hb
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff K).1 hb
    rw [← hθ, h t]

omit [CharP K 2] in
theorem mem_fixed_upper_iff {y : V} :
    (y ∈ Set.range θ ∧ ∀ a ∈ upperUnipotent K, a • y = y) ↔ ∃ s : K, θ ![s, 0] = y := by
  constructor
  · rintro ⟨⟨v, rfl⟩, h⟩
    refine ⟨v 0, congrArg θ ?_⟩
    have h1 := (forall_upper_smul_eq_iff hθ hinj v).1 h
    ext i
    fin_cases i <;> simp [h1]
  · rintro ⟨s, rfl⟩
    exact ⟨⟨_, rfl⟩, (forall_upper_smul_eq_iff hθ hinj _).2 (by simp)⟩

omit [CharP K 2] in
theorem mem_fixed_lower_iff {y : V} :
    (y ∈ Set.range θ ∧ ∀ b ∈ lowerUnipotent K, b • y = y) ↔ ∃ s : K, θ ![0, s] = y := by
  constructor
  · rintro ⟨⟨v, rfl⟩, h⟩
    refine ⟨v 1, congrArg θ ?_⟩
    have h0 := (forall_lower_smul_eq_iff hθ hinj v).1 h
    ext i
    fin_cases i <;> simp [h0]
  · rintro ⟨s, rfl⟩
    exact ⟨⟨_, rfl⟩, (forall_lower_smul_eq_iff hθ hinj _).2 (by simp)⟩

end Embedding

end CFSG.Timmesfeld.ARS.NaturalModule

namespace CFSG.Timmesfeld.ARS

open Matrix CFSG.Timmesfeld.RankOne NaturalModule
open scoped commutatorElement

section Module

variable {K V : Type*} [Field K] [CharP K 2] [PerfectRing K 2] [AddCommGroup V]
  [DistribMulAction (SpecialLinearGroup (Fin 2) K) V]

theorem exists_natural_of_quadratic
    (hfix : ∀ v : V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0)
    (hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {w : V} (hw : ∀ a ∈ upperUnipotent K, a • w = w) (hw0 : w ≠ 0) :
    ∃ θ : (Fin 2 → K) →+ V, Function.Injective θ ∧
      θ.range = AddSubgroup.closure (Set.range fun x : SpecialLinearGroup (Fin 2) K => x • w) ∧
      θ ![1, 0] = w ∧
      ∀ (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
        θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v := by
  have hq : ∀ (s t : K) (v : V), upperElt K s • (upperElt K t • v - v) = upperElt K t • v - v :=
    fun s t v => hquad _ ((mem_upperUnipotent_iff K).2 ⟨t, rfl⟩) _
      ((mem_upperUnipotent_iff K).2 ⟨s, rfl⟩) v
  have hw' : ∀ t : K, upperElt K t • w = w :=
    fun t => hw _ ((mem_upperUnipotent_iff K).2 ⟨t, rfl⟩)
  let θ : (Fin 2 → K) →+ V := AddMonoidHom.mk' (natMap w) (natMap_add hq w)
  have hθ : ∀ (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v := natMap_mulVec hq hfix hw'
  have he : θ ![1, 0] = w := natMap_e₁ hq hfix hw'
  refine ⟨θ, ?_, le_antisymm ?_ ?_, he, hθ⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    obtain ⟨g, hg⟩ := exists_mulVec_eq hne
    rw [← hg, hθ, he] at hv
    exact hw0 ((smul_eq_zero_iff_eq g).1 hv)
  · rintro _ ⟨v, rfl⟩
    by_cases hv : v = 0
    · rw [hv, map_zero]
      exact zero_mem _
    · obtain ⟨g, rfl⟩ := exists_mulVec_eq hv
      rw [hθ, he]
      exact AddSubgroup.subset_closure ⟨g, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, by rw [hθ, he]⟩

theorem fixed_eq_of_quadratic
    (hfix : ∀ v : V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0)
    (hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {w : V} (hw : ∀ a ∈ upperUnipotent K, a • w = w) (hw0 : w ≠ 0) {W CA CB : Set V}
    (hW : W = AddSubgroup.closure (Set.range fun x : SpecialLinearGroup (Fin 2) K => x • w))
    (hCA : CA = {y | y ∈ W ∧ ∀ a ∈ upperUnipotent K, a • y = y})
    (hCB : CB = {y | y ∈ W ∧ ∀ b ∈ lowerUnipotent K, b • y = y}) :
    (∀ a ∈ upperUnipotent K, a ≠ 1 →
      CA = (fun y => a • y - y) '' W ∧ CA = (fun y => a • y - y) '' CB) ∧
    (∀ u ∈ CB, u ≠ 0 →
      CA = (fun a : SpecialLinearGroup (Fin 2) K => a • u - u) '' (upperUnipotent K : Set _)) ∧
    (∀ v ∈ CA, v ≠ 0 → CA = insert 0 ((fun h : SpecialLinearGroup (Fin 2) K => h • v) ''
      ((Subgroup.normalizer (upperUnipotent K : Set (SpecialLinearGroup (Fin 2) K)) ⊓
        Subgroup.normalizer (lowerUnipotent K : Set (SpecialLinearGroup (Fin 2) K)) :
          Subgroup (SpecialLinearGroup (Fin 2) K)) : Set (SpecialLinearGroup (Fin 2) K)))) := by
  obtain ⟨θ, hinj, hrange, he, hθ⟩ := exists_natural_of_quadratic hfix hquad hw hw0
  have hW' : W = Set.range θ := by rw [hW, ← hrange, AddMonoidHom.coe_range]
  subst hW'
  have hCA' : CA = Set.range fun s : K => θ ![s, 0] := by
    ext y
    rw [hCA, Set.mem_ofPred_eq, mem_fixed_upper_iff hθ hinj]
    rfl
  have hCB' : CB = Set.range fun s : K => θ ![0, s] := by
    ext y
    rw [hCB, Set.mem_ofPred_eq, mem_fixed_lower_iff hθ hinj]
    rfl
  have hsub : ∀ (t : K) (v : Fin 2 → K), upperElt K t • θ v - θ v = θ ![t * v 1, 0] :=
    upperElt_smul_sub_eq hθ
  refine ⟨fun a ha ha1 => ?_, fun u hu hu0 => ?_, fun v hv hv0 => ?_⟩
  · obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 ha
    have ht : t ≠ 0 := by
      rintro rfl
      exact ha1 (upperElt_zero K)
    have hmem : ∀ s : K, θ ![s, 0] = upperElt K t • θ ![0, s / t] - θ ![0, s / t] := by
      intro s
      rw [hsub]
      congr 3
      simp [mul_div_cancel₀ _ ht]
    refine ⟨Set.Subset.antisymm ?_ ?_, Set.Subset.antisymm ?_ ?_⟩
    · rw [hCA']
      rintro _ ⟨s, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, (hmem s).symm⟩
    · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      dsimp only
      rw [hCA', hsub]
      exact ⟨_, rfl⟩
    · rw [hCA']
      rintro _ ⟨s, rfl⟩
      exact ⟨_, hCB' ▸ ⟨s / t, rfl⟩, (hmem s).symm⟩
    · rintro _ ⟨_, hy, rfl⟩
      rw [hCB'] at hy
      obtain ⟨s, rfl⟩ := hy
      dsimp only
      rw [hCA', hsub]
      exact ⟨_, rfl⟩
  · rw [hCB'] at hu
    obtain ⟨s, rfl⟩ := hu
    have hs : s ≠ 0 := by
      rintro rfl
      apply hu0
      rw [← map_zero θ, ← vec2_zero]
    apply Set.Subset.antisymm
    · rw [hCA']
      rintro _ ⟨x, rfl⟩
      refine ⟨upperElt K (x / s), (mem_upperUnipotent_iff K).2 ⟨_, rfl⟩, ?_⟩
      simp only
      rw [hsub]
      congr 3
      simp [div_mul_cancel₀ _ hs]
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 ha
      rw [hCA']
      simp only
      rw [hsub]
      exact ⟨_, rfl⟩
  · rw [hCA'] at hv
    obtain ⟨s, rfl⟩ := hv
    have hs : s ≠ 0 := by
      rintro rfl
      apply hv0
      rw [← map_zero θ, ← vec2_zero]
    apply Set.Subset.antisymm
    · rw [hCA']
      rintro _ ⟨x, rfl⟩
      by_cases hx : x = 0
      · left
        rw [hx, ← map_zero θ, ← vec2_zero]
      · right
        refine ⟨diagElt (Units.mk0 x hx * (Units.mk0 s hs)⁻¹),
          ⟨diagElt_mem_normalizer_upperUnipotent _, diagElt_mem_normalizer_lowerUnipotent _⟩, ?_⟩
        simp only
        rw [← hθ, diagElt_mulVec]
        congr 1
        ext i
        fin_cases i <;> simp [hs]
    · rintro _ (rfl | ⟨h, ⟨hA, -⟩, rfl⟩)
      · rw [hCA']
        exact ⟨0, by dsimp only; rw [vec2_zero, map_zero]⟩
      · rw [hCA']
        dsimp only
        have hy : ∀ a ∈ upperUnipotent K, a • θ ![s, 0] = θ ![s, 0] :=
          ((mem_fixed_upper_iff hθ hinj).2 ⟨s, rfl⟩).2
        refine (mem_fixed_upper_iff hθ hinj).1 ⟨⟨_, hθ h _⟩, fun a ha => ?_⟩
        have hmem : h⁻¹ * a * h ∈ upperUnipotent K := by
          have := (Subgroup.mem_normalizer_iff.1 (inv_mem hA) a).1 ha
          rwa [inv_inv] at this
        calc a • h • θ ![s, 0] = h • (h⁻¹ * a * h) • θ ![s, 0] := by
              rw [← mul_smul, ← mul_smul, show h * (h⁻¹ * a * h) = a * h by group]
          _ = h • θ ![s, 0] := by rw [hy _ hmem]

end Module

section Conj

variable {K : Type*} [Field K] {G : Type*} [Group G] {X N : Subgroup G}

@[expose] def NaturalModule.conjSMul (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K)
    (hXN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (g : SpecialLinearGroup (Fin 2) K)
    (v : Additive ↥N) : Additive ↥N :=
  Additive.ofMul ⟨(φ.symm g : G) * (v.toMul : G) * (φ.symm g : G)⁻¹,
    hXN _ (φ.symm g).2 _ v.toMul.2⟩

@[reducible] def NaturalModule.conjAction (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K)
    (hXN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    DistribMulAction (SpecialLinearGroup (Fin 2) K) (Additive ↥N) where
  smul := NaturalModule.conjSMul φ hXN
  one_smul v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show (φ.symm 1 : G) * (v.toMul : G) * (φ.symm 1 : G)⁻¹ = v.toMul
    simp
  mul_smul g h v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show (φ.symm (g * h) : G) * (v.toMul : G) * (φ.symm (g * h) : G)⁻¹ =
      (φ.symm g : G) * ((φ.symm h : G) * (v.toMul : G) * (φ.symm h : G)⁻¹) * (φ.symm g : G)⁻¹
    simp [mul_assoc]
  smul_zero g := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show (φ.symm g : G) * ((1 : N) : G) * (φ.symm g : G)⁻¹ = ((1 : N) : G)
    simp
  smul_add g v v' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show (φ.symm g : G) * ((v.toMul : G) * (v'.toMul : G)) * (φ.symm g : G)⁻¹ =
      ((φ.symm g : G) * (v.toMul : G) * (φ.symm g : G)⁻¹) *
        ((φ.symm g : G) * (v'.toMul : G) * (φ.symm g : G)⁻¹)
    group

structure IsNaturalModule (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K) (θ : (Fin 2 → K) → G) :
    Prop where
  map_add : ∀ v v', θ (v + v') = θ v * θ v'
  injective : Function.Injective θ
  map_mulVec : ∀ (x : X) (v : Fin 2 → K),
    θ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = (x : G) * θ v * (x : G)⁻¹

theorem exists_natural_of_quadratic_conj [CharP K 2] [PerfectRing K 2]
    (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K) {A : Subgroup G}
    (hA : (A.subgroupOf X).map φ.toMonoidHom = upperUnipotent K)
    (hN : ∀ n ∈ N, ∀ m ∈ N, Commute n m) (hXN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hfix : ∀ n ∈ N, (∀ x ∈ X, Commute x n) → n = 1)
    (hquad : ∀ n ∈ N, ∀ a ∈ A, ∀ a' ∈ A, Commute a' ⁅a, n⁆)
    {w : G} (hwN : w ∈ N) (hwA : ∀ a ∈ A, Commute a w) (hw1 : w ≠ 1) :
    ∃ θ : (Fin 2 → K) → G, IsNaturalModule φ θ ∧
      Set.range θ = Subgroup.closure (Set.range fun x : X => (x : G) * w * (x : G)⁻¹) ∧
      θ ![1, 0] = w := by
  let _ : AddCommGroup (Additive ↥N) :=
    { (inferInstance : AddGroup (Additive ↥N)) with
      add_comm := fun a b => Additive.toMul.injective (Subtype.ext (hN _ a.toMul.2 _ b.toMul.2)) }
  let _ := NaturalModule.conjAction φ hXN
  let ι : Additive ↥N → G := fun v => ((v.toMul : N) : G)
  have hι_inj : Function.Injective ι := fun a b h => Additive.toMul.injective (Subtype.ext h)
  have hsmul : ∀ (g : SpecialLinearGroup (Fin 2) K) (v : Additive ↥N),
      ι (g • v) = (φ.symm g : G) * ι v * (φ.symm g : G)⁻¹ := fun _ _ => rfl
  have hsub : ∀ a b : Additive ↥N, ι (a - b) = ι a * (ι b)⁻¹ := by
    intro a b
    show ((a.toMul / b.toMul : N) : G) = _
    rw [Subgroup.coe_div, div_eq_mul_inv]
  have hmemA : ∀ a ∈ upperUnipotent K, ((φ.symm a : X) : G) ∈ A := by
    intro a ha
    rw [← hA] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    simpa [Subgroup.mem_subgroupOf] using hy
  have hfix' : ∀ v : Additive ↥N, (∀ g : SpecialLinearGroup (Fin 2) K, g • v = v) → v = 0 := by
    intro v hv
    apply hι_inj
    refine hfix _ v.toMul.2 fun x hx => mul_inv_eq_iff_eq_mul.1 ?_
    have h := congrArg ι (hv (φ ⟨x, hx⟩))
    rwa [hsmul, MulEquiv.symm_apply_apply] at h
  have hquad' : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : Additive ↥N,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    apply hι_inj
    have hz : ι (a • v - v) = ⁅((φ.symm a : X) : G), ι v⁆ := by
      rw [hsub, hsmul, commutatorElement_def]
    rw [hsmul, hz, (hquad _ v.toMul.2 _ (hmemA a ha) _ (hmemA a' ha')).eq, mul_inv_cancel_right]
  let w' : Additive ↥N := Additive.ofMul ⟨w, hwN⟩
  have hw' : ∀ a ∈ upperUnipotent K, a • w' = w' := by
    intro a ha
    apply hι_inj
    rw [hsmul]
    show ((φ.symm a : X) : G) * w * ((φ.symm a : X) : G)⁻¹ = w
    rw [(hwA _ (hmemA a ha)).eq, mul_inv_cancel_right]
  have hw0' : w' ≠ 0 := fun h => hw1 (congrArg ι h)
  obtain ⟨θ₀, hinj, -, he, hθ⟩ := exists_natural_of_quadratic hfix' hquad' hw' hw0'
  have he' : ι (θ₀ ![1, 0]) = w := by rw [he]; rfl
  have hθ' : ∀ (x : X) (v : Fin 2 → K),
      ι (θ₀ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) = (x : G) * ι (θ₀ v) * (x : G)⁻¹ := by
    intro x v
    rw [hθ, hsmul, MulEquiv.symm_apply_apply]
  refine ⟨fun v => ι (θ₀ v), ⟨fun v v' => by
    show ι (θ₀ (v + v')) = ι (θ₀ v) * ι (θ₀ v')
    rw [map_add]
    rfl, hι_inj.comp hinj, hθ'⟩, Set.Subset.antisymm ?_ ?_, he'⟩
  · rintro _ ⟨v, rfl⟩
    by_cases hv : v = 0
    · show ι (θ₀ v) ∈ _
      rw [hv, map_zero]
      exact Subgroup.one_mem _
    · obtain ⟨g, rfl⟩ := exists_mulVec_eq hv
      have hg : g = φ (φ.symm g) := (MulEquiv.apply_symm_apply φ g).symm
      dsimp only
      rw [hg, hθ', he']
      exact Subgroup.subset_closure ⟨_, rfl⟩
  · intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      exact ⟨(φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0], by dsimp only; rw [hθ', he']⟩
    | one => exact ⟨0, by dsimp only; rw [map_zero]; rfl⟩
    | mul y z _ _ hy hz =>
      obtain ⟨v, rfl⟩ := hy
      obtain ⟨v', rfl⟩ := hz
      exact ⟨v + v', by dsimp only; rw [map_add]; rfl⟩
    | inv y _ hy =>
      obtain ⟨v, rfl⟩ := hy
      exact ⟨-v, by dsimp only; rw [map_neg]; rfl⟩

theorem NaturalModule.coe_mem_iff {φ : ↥X ≃* SpecialLinearGroup (Fin 2) K} {H : Subgroup G}
    {S : Subgroup (SpecialLinearGroup (Fin 2) K)} (hH : (H.subgroupOf X).map φ.toMonoidHom = S)
    (x : X) : (x : G) ∈ H ↔ φ x ∈ S := by
  rw [← hH, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, by rwa [Subgroup.mem_subgroupOf], rfl⟩
  · rintro ⟨y, hy, hxy⟩
    obtain rfl : y = x := φ.injective hxy
    rwa [Subgroup.mem_subgroupOf] at hy

theorem NaturalModule.coe_mem_normalizer {φ : ↥X ≃* SpecialLinearGroup (Fin 2) K}
    {H : Subgroup G} {S : Subgroup (SpecialLinearGroup (Fin 2) K)}
    (hH : (H.subgroupOf X).map φ.toMonoidHom = S) (hHX : H ≤ X) {h : X}
    (hh : φ h ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 2) K))) :
    (h : G) ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have key := (Subgroup.mem_normalizer_iff.1 hh (φ ⟨g, hHX hg⟩)).1 ((coe_mem_iff hH _).1 hg)
    have : (h : G) * g * (h : G)⁻¹ = ((h * ⟨g, hHX hg⟩ * h⁻¹ : X) : G) := rfl
    rw [this, coe_mem_iff hH]
    simpa only [map_mul, map_inv] using key
  · intro hg
    have hgX : g ∈ X := by
      have h1 : (h : G) * g * (h : G)⁻¹ ∈ X := hHX hg
      have : g = (h : G)⁻¹ * ((h : G) * g * (h : G)⁻¹) * (h : G) := by group
      rw [this]
      exact X.mul_mem (X.mul_mem (X.inv_mem h.2) h1) h.2
    have hmem : ((h * ⟨g, hgX⟩ * h⁻¹ : X) : G) ∈ H := hg
    rw [coe_mem_iff hH] at hmem
    rw [show g = ((⟨g, hgX⟩ : X) : G) from rfl, coe_mem_iff hH]
    refine (Subgroup.mem_normalizer_iff.1 hh _).2 ?_
    simpa only [map_mul, map_inv] using hmem

namespace IsNaturalModule

variable {φ : ↥X ≃* SpecialLinearGroup (Fin 2) K} {θ : (Fin 2 → K) → G}
  (hθ : IsNaturalModule φ θ)
include hθ

theorem map_zero : θ 0 = 1 := by
  have h := hθ.map_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem map_neg (v : Fin 2 → K) : θ (-v) = (θ v)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hθ.map_add, neg_add_cancel, hθ.map_zero])

theorem map_sub (v v' : Fin 2 → K) : θ (v - v') = θ v * (θ v')⁻¹ := by
  rw [sub_eq_add_neg, hθ.map_add, hθ.map_neg]

theorem commutatorElement_eq (x : X) (v : Fin 2 → K) :
    ⁅(x : G), θ v⁆ = θ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v) := by
  rw [commutatorElement_def, hθ.map_sub, hθ.map_mulVec]

theorem commute_iff (x : X) (v : Fin 2 → K) :
    Commute (x : G) (θ v) ↔ (φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
  rw [← hθ.injective.eq_iff, hθ.map_mulVec, Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]

theorem card_range : Nat.card (Set.range θ) = Nat.card K ^ 2 := by
  rw [← Nat.card_congr (Equiv.ofInjective θ hθ.injective), Nat.card_fun, Nat.card_fin]

theorem card_eq {N : Subgroup G} (hN : (N : Set G) = Set.range θ) :
    Nat.card N = Nat.card K ^ 2 := by
  rw [← hθ.card_range, ← hN]
  rfl

theorem eq_one_of_forall_commute {x : X} (hx : ∀ v : Fin 2 → K, Commute (x : G) (θ v)) :
    x = 1 := by
  have h1 : φ x = 1 :=
    NaturalModule.eq_one_of_forall_mulVec_eq fun v => (hθ.commute_iff x v).1 (hx v)
  exact φ.injective (h1.trans (map_one φ).symm)

theorem exists_conj_eq {u v : Fin 2 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ x : X, (x : G) * θ u * (x : G)⁻¹ = θ v := by
  obtain ⟨g, rfl⟩ := NaturalModule.exists_mulVec_eq hu
  obtain ⟨g', rfl⟩ := NaturalModule.exists_mulVec_eq hv
  refine ⟨φ.symm (g' * g⁻¹), ?_⟩
  rw [← hθ.map_mulVec, MulEquiv.apply_symm_apply, Matrix.mulVec_mulVec]
  congr 2
  change ((g' * g⁻¹ * g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [inv_mul_cancel_right]

variable {A B : Subgroup G} (hA : (A.subgroupOf X).map φ.toMonoidHom = upperUnipotent K)
  (hAX : A ≤ X) (hB : (B.subgroupOf X).map φ.toMonoidHom = lowerUnipotent K) (hBX : B ≤ X)

include hA hAX in
theorem forall_commute_upper_iff (v : Fin 2 → K) :
    (∀ a ∈ A, Commute a (θ v)) ↔ v 1 = 0 := by
  rw [← forall_upperElt_mulVec_eq_iff]
  constructor
  · intro h t
    have hx : ((φ.symm (upperElt K t) : X) : G) ∈ A :=
      (coe_mem_iff hA _).2 (by
        rw [MulEquiv.apply_symm_apply]
        exact (mem_upperUnipotent_iff K).2 ⟨t, rfl⟩)
    have := (hθ.commute_iff _ v).1 (h _ hx)
    rwa [MulEquiv.apply_symm_apply] at this
  · intro h a ha
    obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff K).1 ((coe_mem_iff hA ⟨a, hAX ha⟩).1 ha)
    exact (hθ.commute_iff ⟨a, hAX ha⟩ v).2 ((congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ht).trans (h t))

include hB hBX in
theorem forall_commute_lower_iff (v : Fin 2 → K) :
    (∀ b ∈ B, Commute b (θ v)) ↔ v 0 = 0 := by
  rw [← forall_lowerElt_mulVec_eq_iff]
  constructor
  · intro h t
    have hx : ((φ.symm (lowerElt K t) : X) : G) ∈ B :=
      (coe_mem_iff hB _).2 (by
        rw [MulEquiv.apply_symm_apply]
        exact (mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩)
    have := (hθ.commute_iff _ v).1 (h _ hx)
    rwa [MulEquiv.apply_symm_apply] at this
  · intro h b hb
    obtain ⟨t, ht⟩ := (mem_lowerUnipotent_iff K).1 ((coe_mem_iff hB ⟨b, hBX hb⟩).1 hb)
    exact (hθ.commute_iff ⟨b, hBX hb⟩ v).2 ((congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ht).trans (h t))

include hA hAX in
theorem mem_fixed_upper_iff {y : G} :
    (y ∈ Set.range θ ∧ ∀ a ∈ A, Commute a y) ↔ ∃ s : K, θ ![s, 0] = y := by
  constructor
  · rintro ⟨⟨v, rfl⟩, h⟩
    refine ⟨v 0, congrArg θ ?_⟩
    have h1 := (hθ.forall_commute_upper_iff hA hAX v).1 h
    ext i
    fin_cases i <;> simp [h1]
  · rintro ⟨s, rfl⟩
    exact ⟨⟨_, rfl⟩, (hθ.forall_commute_upper_iff hA hAX _).2 (by simp)⟩

include hB hBX in
theorem mem_fixed_lower_iff {y : G} :
    (y ∈ Set.range θ ∧ ∀ b ∈ B, Commute b y) ↔ ∃ s : K, θ ![0, s] = y := by
  constructor
  · rintro ⟨⟨v, rfl⟩, h⟩
    refine ⟨v 1, congrArg θ ?_⟩
    have h0 := (hθ.forall_commute_lower_iff hB hBX v).1 h
    ext i
    fin_cases i <;> simp [h0]
  · rintro ⟨s, rfl⟩
    exact ⟨⟨_, rfl⟩, (hθ.forall_commute_lower_iff hB hBX _).2 (by simp)⟩

include hA hAX in
theorem commutatorElement_upper {a : G} (ha : a ∈ A) :
    ∃ t : K, (a = 1 ↔ t = 0) ∧ ∀ v : Fin 2 → K, ⁅a, θ v⁆ = θ ![t * v 1, 0] := by
  obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff K).1 ((coe_mem_iff hA ⟨a, hAX ha⟩).1 ha)
  refine ⟨t, ⟨fun h1 => ?_, fun h0 => ?_⟩, fun v => ?_⟩
  · apply upperElt_injective K
    rw [upperElt_zero, ← ht]
    have : (⟨a, hAX ha⟩ : X) = 1 := Subtype.ext h1
    rw [this]
    exact map_one φ
  · rw [h0, upperElt_zero] at ht
    have : (⟨a, hAX ha⟩ : X) = 1 := φ.injective (ht.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  · have key : (φ ⟨a, hAX ha⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v = ![t * v 1, 0] := by
      rw [← upperElt_mulVec_sub]
      exact congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
        (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v) ht
    rw [← key]
    exact hθ.commutatorElement_eq ⟨a, hAX ha⟩ v

include hA hAX hB hBX in
theorem fixed_eq {W CA CB : Set G} (hW : W = Set.range θ)
    (hCA : CA = {y | y ∈ W ∧ ∀ a ∈ A, Commute a y})
    (hCB : CB = {y | y ∈ W ∧ ∀ b ∈ B, Commute b y}) :
    (∀ a ∈ A, a ≠ 1 → CA = (fun y => ⁅a, y⁆) '' W ∧ CA = (fun y => ⁅a, y⁆) '' CB) ∧
    (∀ u ∈ CB, u ≠ 1 → CA = (fun a => ⁅a, u⁆) '' (A : Set G)) ∧
    (∀ v ∈ CA, v ≠ 1 → CA = insert 1 ((fun h => h * v * h⁻¹) ''
      ((X ⊓ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) : Subgroup G) :
        Set G))) := by
  subst hW
  have hCA' : CA = Set.range fun s : K => θ ![s, 0] := by
    ext y
    rw [hCA, Set.mem_ofPred_eq, hθ.mem_fixed_upper_iff hA hAX]
    rfl
  have hCB' : CB = Set.range fun s : K => θ ![0, s] := by
    ext y
    rw [hCB, Set.mem_ofPred_eq, hθ.mem_fixed_lower_iff hB hBX]
    rfl
  have hzero : θ ![0, 0] = 1 := by rw [NaturalModule.vec2_zero, hθ.map_zero]
  refine ⟨fun a ha ha1 => ?_, fun u hu hu1 => ?_, fun v hv hv1 => ?_⟩
  · obtain ⟨t, ht1, hcomm⟩ := hθ.commutatorElement_upper hA hAX ha
    have ht : t ≠ 0 := fun h => ha1 (ht1.2 h)
    have hmem : ∀ s : K, θ ![s, 0] = ⁅a, θ ![0, s / t]⁆ := by
      intro s
      rw [hcomm]
      congr 3
      simp [mul_div_cancel₀ _ ht]
    refine ⟨Set.Subset.antisymm ?_ ?_, Set.Subset.antisymm ?_ ?_⟩
    · rw [hCA']
      rintro _ ⟨s, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, (hmem s).symm⟩
    · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      dsimp only
      rw [hCA', hcomm]
      exact ⟨_, rfl⟩
    · rw [hCA']
      rintro _ ⟨s, rfl⟩
      exact ⟨_, hCB' ▸ ⟨s / t, rfl⟩, (hmem s).symm⟩
    · rintro _ ⟨_, hy, rfl⟩
      rw [hCB'] at hy
      obtain ⟨s, rfl⟩ := hy
      dsimp only
      rw [hCA', hcomm]
      exact ⟨_, rfl⟩
  · rw [hCB'] at hu
    obtain ⟨s, rfl⟩ := hu
    have hs : s ≠ 0 := by
      rintro rfl
      exact hu1 hzero
    apply Set.Subset.antisymm
    · rw [hCA']
      rintro _ ⟨x, rfl⟩
      have hx : ((φ.symm (upperElt K (x / s)) : X) : G) ∈ A :=
        (coe_mem_iff hA _).2 (by
          rw [MulEquiv.apply_symm_apply]
          exact (mem_upperUnipotent_iff K).2 ⟨_, rfl⟩)
      refine ⟨_, hx, ?_⟩
      dsimp only
      rw [hθ.commutatorElement_eq, MulEquiv.apply_symm_apply, upperElt_mulVec_sub]
      congr 3
      simp [div_mul_cancel₀ _ hs]
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨t, -, hcomm⟩ := hθ.commutatorElement_upper hA hAX ha
      dsimp only
      rw [hCA', hcomm]
      exact ⟨_, rfl⟩
  · rw [hCA'] at hv
    obtain ⟨s, rfl⟩ := hv
    have hs : s ≠ 0 := by
      rintro rfl
      exact hv1 hzero
    apply Set.Subset.antisymm
    · rw [hCA']
      rintro _ ⟨x, rfl⟩
      by_cases hx : x = 0
      · left
        dsimp only
        rw [hx, hzero]
      · right
        set c : Kˣ := Units.mk0 x hx * (Units.mk0 s hs)⁻¹
        set h : X := φ.symm (diagElt c)
        have hφh : φ h = diagElt c := MulEquiv.apply_symm_apply φ _
        refine ⟨(h : G), ⟨⟨h.2, coe_mem_normalizer hA hAX ?_⟩, coe_mem_normalizer hB hBX ?_⟩, ?_⟩
        · rw [hφh]
          exact diagElt_mem_normalizer_upperUnipotent c
        · rw [hφh]
          exact diagElt_mem_normalizer_lowerUnipotent c
        · dsimp only
          rw [← hθ.map_mulVec, hφh, diagElt_mulVec]
          congr 1
          ext i
          fin_cases i <;> simp [c, hs]
    · rintro _ (rfl | ⟨h, ⟨⟨hX, hhA⟩, -⟩, rfl⟩)
      · rw [hCA']
        exact ⟨0, hzero⟩
      · have hy : ∀ a ∈ A, Commute a (θ ![s, 0]) :=
          ((hθ.mem_fixed_upper_iff hA hAX).2 ⟨s, rfl⟩).2
        rw [hCA']
        refine (hθ.mem_fixed_upper_iff hA hAX).1 ⟨⟨_, (hθ.map_mulVec ⟨h, hX⟩ _)⟩, fun a ha => ?_⟩
        have hmem : h⁻¹ * a * h ∈ A := by
          have := (Subgroup.mem_normalizer_iff.1 (inv_mem hhA) a).1 ha
          rwa [inv_inv] at this
        have hc := hy _ hmem
        rw [Commute, SemiconjBy] at hc ⊢
        calc a * (h * θ ![s, 0] * h⁻¹) = h * ((h⁻¹ * a * h) * θ ![s, 0]) * h⁻¹ := by group
          _ = h * (θ ![s, 0] * (h⁻¹ * a * h)) * h⁻¹ := by rw [hc]
          _ = h * θ ![s, 0] * h⁻¹ * a := by group

end IsNaturalModule

end Conj

end CFSG.Timmesfeld.ARS
