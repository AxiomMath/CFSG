module

public import CFSG.RankThree.PartOne.K133C.SpForm

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix

set_option linter.unusedSectionVars false

section Eichler

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

structure PolarQuad (Q : (ι → K) → K) (J : Matrix ι ι K) : Prop where
  add : ∀ x y, Q (x + y) = Q x + Q y + bf J x y
  smul : ∀ (c : K) (x : ι → K), Q (c • x) = c ^ 2 * Q x
  symm : Jᵀ = J
  nondeg : ∀ w : ι → K, J *ᵥ w = 0 → w = 0

variable {Q : (ι → K) → K} {J : Matrix ι ι K}

theorem PolarQuad.zero (h : PolarQuad Q J) : Q 0 = 0 := by
  have := h.smul 0 0
  rw [zero_smul, zero_pow two_ne_zero, zero_mul] at this
  exact this

theorem PolarQuad.alt [CharP K 2] (h : PolarQuad Q J) (y : ι → K) : y ⬝ᵥ (J *ᵥ y) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 := h.add y y
  rw [← two_smul K y, h.smul] at h1
  change bf J y y = 0
  linear_combination (-1 : K) * h1 + Q y * h2

@[expose] def eichM (J : Matrix ι ι K) (Q : (ι → K) → K) (s w : ι → K) : Matrix ι ι K :=
  sglM J s w + Q w • vecMulVec s (J *ᵥ s)

theorem eichM_mulVec (s w y : ι → K) :
    eichM J Q s w *ᵥ y = y + bf J y s • w + bf J y w • s + (Q w * bf J y s) • s := by
  have h1 : (J *ᵥ s) ⬝ᵥ y = bf J y s := dotProduct_comm _ _
  rw [eichM, add_mulVec, sglM_mulVec, smul_mulVec, vecMulVec_mulVec', h1, smul_smul]

theorem eichM_zero (h : PolarQuad Q J) (s : ι → K) : eichM J Q s 0 = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [eichM_mulVec, one_mulVec, h.zero, bf_zero_right]
  simp

variable [CharP K 2]

theorem eichM_map (h : PolarQuad Q J) {s w : ι → K} (hs : Q s = 0) (hsw : bf J s w = 0) (y : ι → K) :
    Q (eichM J Q s w *ᵥ y) = Q y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hws : bf J w s = 0 := by rw [bf_comm J h.symm]; exact hsw
  rw [eichM_mulVec]
  have e1 : y + bf J y s • w + bf J y w • s + (Q w * bf J y s) • s =
      y + (bf J y s • w + (bf J y w + Q w * bf J y s) • s) := by module
  rw [e1, h.add y, h.add (bf J y s • w), h.smul, h.smul]
  simp only [bf_add_right, bf_smul_right, bf_smul_left, hws, hs]
  linear_combination (bf J y s ^ 2 * Q w + bf J y s * bf J y w) * h2

theorem eichM_mul (h : PolarQuad Q J) {s w w' : ι → K} (hsw : bf J s w = 0)
    (hsw' : bf J s w' = 0) : eichM J Q s w * eichM J Q s w' = eichM J Q s (w + w') := by
  have hss : bf J s s = 0 := h.alt s
  have hws : bf J w s = 0 := by rw [bf_comm J h.symm]; exact hsw
  have hw's : bf J w' s = 0 := by rw [bf_comm J h.symm]; exact hsw'
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [← mulVec_mulVec, eichM_mulVec s w' y, eichM_mulVec s w, eichM_mulVec s (w + w') y]
  simp only [bf_add_left, bf_add_right, bf_smul_left, hss, hw's, hsw, bf_comm J h.symm w' w,
    h.add w w']
  module

theorem eichM_mul_self (h : PolarQuad Q J) {s w : ι → K} (hsw : bf J s w = 0) :
    eichM J Q s w * eichM J Q s w = 1 := by
  have hww : w + w = 0 := by rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  rw [eichM_mul h hsw hsw, hww, eichM_zero h]

@[expose] def orthSub (Q : (ι → K) → K) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
  one_mem' := fun v => by simp
  mul_mem' := fun {a b} ha hb v => by
    rw [Units.val_mul, ← mulVec_mulVec, ha, hb]
  inv_mem' := fun {a} ha v => by
    have := ha (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    rw [mulVec_inv_mulVec] at this
    exact this.symm

theorem bf_map_of_mem_orthSub (h : PolarQuad Q J) {g : GL ι K} (hg : g ∈ orthSub Q) (x y : ι → K) :
    bf J ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) = bf J x y := by
  have h1 := h.add ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y)
  rw [← mulVec_add, hg, hg, hg, h.add x y] at h1
  have : Q x + Q y + bf J x y = Q x + Q y + bf J ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) := h1
  exact (add_left_cancel this).symm

open _root_.Classical in
@[expose] noncomputable def eichGL (h : PolarQuad Q J) (s w : ι → K) : GL ι K :=
  if hsw : bf J s w = 0 then
    ⟨eichM J Q s w, eichM J Q s w, eichM_mul_self h hsw, eichM_mul_self h hsw⟩
  else 1

theorem coe_eichGL (h : PolarQuad Q J) {s w : ι → K} (hsw : bf J s w = 0) :
    ((eichGL h s w : GL ι K) : Matrix ι ι K) = eichM J Q s w := by
  rw [eichGL, dite_eq_left hsw]

theorem eichGL_mem_orthSub (h : PolarQuad Q J) {s w : ι → K} (hs : Q s = 0) (hsw : bf J s w = 0) :
    eichGL h s w ∈ orthSub Q := fun y => by
  rw [coe_eichGL h hsw]
  exact eichM_map h hs hsw y

theorem conj_eichGL (h : PolarQuad Q J) {g : GL ι K} (hg : g ∈ orthSub Q) {s w : ι → K}
    (hs : Q s = 0) (hsw : bf J s w = 0) :
    g * eichGL h s w * g⁻¹ = eichGL h ((g : Matrix ι ι K) *ᵥ s) ((g : Matrix ι ι K) *ᵥ w) := by
  have hgs : Q ((g : Matrix ι ι K) *ᵥ s) = 0 := by rw [hg, hs]
  have hgsw : bf J ((g : Matrix ι ι K) *ᵥ s) ((g : Matrix ι ι K) *ᵥ w) = 0 := by
    rw [bf_map_of_mem_orthSub h hg]; exact hsw
  have hQw : Q ((g : Matrix ι ι K) *ᵥ w) = Q w := hg w
  have hiso := bf_map_of_mem_orthSub h hg
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro y
  have h1 := hiso (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) s
  have h2 := hiso (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) w
  rw [mulVec_inv_mulVec] at h1 h2
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, coe_eichGL h hsw,
    eichM_mulVec, mulVec_add, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul,
    mulVec_inv_mulVec, ← h1, ← h2, coe_eichGL h hgsw, eichM_mulVec, hQw]

theorem eichGL_inj (h : PolarQuad Q J) {s w w' : ι → K} (hs0 : s ≠ 0) (hsw : bf J s w = 0)
    (hsw' : bf J s w' = 0) (heq : eichGL h s w = eichGL h s w') : ∃ c : K, w' - w = c • s := by
  obtain ⟨y₀, hy₀⟩ := exists_bf_ne_zero J h.nondeg hs0
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ y₀) heq
  simp only [coe_eichGL h hsw, coe_eichGL h hsw', eichM_mulVec] at h1
  set b := bf J y₀ s with hb
  have h3 : (y₀ + b • w' + bf J y₀ w' • s + (Q w' * b) • s) -
      (y₀ + b • w + bf J y₀ w • s + (Q w * b) • s) = 0 := sub_eq_zero.2 h1.symm
  have h4 : b • (w' - w) = (bf J y₀ w - bf J y₀ w' + (Q w - Q w') * b) • s := by
    calc b • (w' - w) = ((y₀ + b • w' + bf J y₀ w' • s + (Q w' * b) • s) -
          (y₀ + b • w + bf J y₀ w • s + (Q w * b) • s)) +
          ((bf J y₀ w - bf J y₀ w' + (Q w - Q w') * b) • s) := by module
      _ = (bf J y₀ w - bf J y₀ w' + (Q w - Q w') * b) • s := by rw [h3, zero_add]
  refine ⟨b⁻¹ * (bf J y₀ w - bf J y₀ w' + (Q w - Q w') * b), ?_⟩
  apply smul_right_injective (ι → K) hy₀
  show b • (w' - w) = b • ((b⁻¹ * (bf J y₀ w - bf J y₀ w' + (Q w - Q w') * b)) • s)
  rw [h4, smul_smul, ← mul_assoc, mul_inv_cancel₀ hy₀, one_mul]

theorem eichGL_mem_radFlag (h : PolarQuad Q J) {s w : ι → K} (hsw : bf J s w = 0)
    (hψs : (J *ᵥ s) ⬝ᵥ s = 0) : eichGL h s w ∈ radFlag s (J *ᵥ s) hψs := by
  have hss : bf J s s = 0 := h.alt s
  have hws : bf J w s = 0 := by rw [bf_comm J h.symm]; exact hsw
  rw [mem_radFlag, coe_eichGL h hsw]
  have hψ : ∀ y, (J *ᵥ s) ⬝ᵥ y = bf J y s := fun y => dotProduct_comm _ _
  refine ⟨?_, fun y => ?_, fun y hy => ?_⟩
  · rw [eichM_mulVec, hss, hsw]
    simp
  · rw [eichM_mulVec]
    have e : y + bf J y s • w + bf J y w • s + (Q w * bf J y s) • s - y =
        bf J y s • w + (bf J y w + Q w * bf J y s) • s := by module
    rw [e, dotProduct_add, dotProduct_smul, dotProduct_smul, hψ w, hψ s, hws, hss]
    simp
  · refine ⟨bf J y w, ?_⟩
    rw [hψ] at hy
    rw [eichM_mulVec, hy]
    simp

end Eichler

end CFSG.RankThree.PartOne.K133C
