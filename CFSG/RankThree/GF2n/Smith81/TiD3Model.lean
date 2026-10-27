module

public import CFSG.RankThree.GF2n.Smith81.TiD2Alg
public import TauCeti.FieldTheory.Finite.FrobeniusFixed

public section

namespace CFSG.RankThree.GF2n.Smith81

section

open Matrix
open scoped MatrixGroups

namespace D3

abbrev Hyp (F : Type*) := Fin 2 → Fin 2 → Fin 2 → F

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[expose] def kForm (τ : F →ₐ[K] F) : Submodule K (Hyp F) where
  carrier := {x | ∀ i j k, x k i j = τ (x i j k)}
  add_mem' := fun {x y} hx hy i j k => by
    simp only [Pi.add_apply, hx i j k, hy i j k, map_add]
  zero_mem' := fun i j k => by simp
  smul_mem' := fun c x hx i j k => by
    simp only [Pi.smul_apply, hx i j k, map_smul]

@[expose] def act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) : Hyp F := fun i j k =>
  ∑ i' : Fin 2, ∑ j' : Fin 2, ∑ k' : Fin 2,
    g i i' * τ (g j j') * τ (τ (g k k')) * x i' j' k'

@[expose] def quad (x : Hyp F) : F :=
  x 0 0 0 * x 1 1 1 + x 0 0 1 * x 1 1 0 + x 0 1 0 * x 1 0 1 + x 1 0 0 * x 0 1 1

@[expose] def polar (x y : Hyp F) : F :=
  x 0 0 0 * y 1 1 1 + x 1 1 1 * y 0 0 0 + x 0 0 1 * y 1 1 0 + x 1 1 0 * y 0 0 1 +
    x 0 1 0 * y 1 0 1 + x 1 0 1 * y 0 1 0 + x 1 0 0 * y 0 1 1 + x 0 1 1 * y 1 0 0

theorem quad_add (x y : Hyp F) : quad (x + y) = quad x + quad y + polar x y := by
  simp only [quad, polar, Pi.add_apply]
  ring

@[expose] def e0 (F : Type*) [Field F] : Hyp F := fun i j k =>
  if i = 0 ∧ j = 0 ∧ k = 0 then 1 else 0

theorem act_uSL_000 (τ : F →+* F) (a : F) (x : Hyp F) :
    act τ ((D2.uSL a : SL(2, F)) : Mat2 F) x 0 0 0 =
      x 0 0 0 + a * x 1 0 0 + τ a * x 0 1 0 + a * τ a * x 1 1 0 + τ (τ a) * x 0 0 1 +
        a * τ (τ a) * x 1 0 1 + τ a * τ (τ a) * x 0 1 1 + a * τ a * τ (τ a) * x 1 1 1 := by
  simp [act, Fin.sum_univ_two]
  ring

open Polynomial in
theorem coords_zero_of_fixed [Fintype F] {q : ℕ} (hq : 2 ≤ q) (hF : Fintype.card F = q ^ 3)
    (τ : F →+* F) (hτ : ∀ a, τ a = a ^ q) (x : Hyp F)
    (hfix : ∀ a : F, act τ ((D2.uSL a : SL(2, F)) : Mat2 F) x 0 0 0 = x 0 0 0) :
    ∀ i j k, ¬ (i = 0 ∧ j = 0 ∧ k = 0) → x i j k = 0 := by
  have hq2 : 2 * q ≤ q ^ 2 := by nlinarith
  have hdeg3 : 1 + q + q ^ 2 < q ^ 3 := by nlinarith
  set P : F[X] := C (x 1 0 0) * X ^ 1 + C (x 0 1 0) * X ^ q + C (x 1 1 0) * X ^ (1 + q) +
    C (x 0 0 1) * X ^ (q ^ 2) + C (x 1 0 1) * X ^ (1 + q ^ 2) + C (x 0 1 1) * X ^ (q + q ^ 2) +
    C (x 1 1 1) * X ^ (1 + q + q ^ 2) with hP
  have hev : ∀ a : F, P.eval a = 0 := by
    intro a
    have h := hfix a
    rw [act_uSL_000, hτ, hτ] at h
    have e1 : (a ^ q) ^ q = a ^ (q ^ 2) := by rw [← pow_mul, sq]
    rw [e1] at h
    simp only [hP, eval_add, eval_mul, eval_C, eval_X, eval_pow, pow_add, pow_one]
    linear_combination h
  have hdeg : P.natDegree ≤ 1 + q + q ^ 2 := by
    rw [hP]
    repeat' apply natDegree_add_le_of_degree_le
    all_goals refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    all_goals omega
  have hP0 : P = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := id) Function.injective_id hev
      (by rw [hF]; exact lt_of_le_of_lt hdeg hdeg3)
  have hc : ∀ n, P.coeff n = 0 := fun n => by rw [hP0]; simp
  have hcoef : ∀ n, P.coeff n = (if n = 1 then x 1 0 0 else 0) + (if n = q then x 0 1 0 else 0) +
      (if n = 1 + q then x 1 1 0 else 0) + (if n = q ^ 2 then x 0 0 1 else 0) +
      (if n = 1 + q ^ 2 then x 1 0 1 else 0) + (if n = q + q ^ 2 then x 0 1 1 else 0) +
      (if n = 1 + q + q ^ 2 then x 1 1 1 else 0) := by
    intro n
    simp only [hP, coeff_add, coeff_C_mul_X_pow]
  have c001 : x 0 0 1 = 0 := by
    have h := hc (q ^ 2)
    rw [hcoef] at h
    simp (disch := omega) [if_neg] at h
    exact h
  have c010 : x 0 1 0 = 0 := by
    have h := hc (q)
    rw [hcoef] at h
    simp (disch := omega) [if_neg] at h
    exact h
  have c011 : x 0 1 1 = 0 := by
    have h := hc (q + q ^ 2)
    rw [hcoef] at h
    simp (disch := omega) [if_neg] at h
    exact h
  have c100 : x 1 0 0 = 0 := by
    have h := hc (1)
    rw [hcoef] at h
    simp (disch := omega) [if_neg] at h
    exact h
  have c101 : x 1 0 1 = 0 := by
    have h := hc (1 + q ^ 2)
    rw [hcoef] at h
    simp (disch := omega) [if_neg] at h
    exact h
  have c110 : x 1 1 0 = 0 := by
    have h := hc (1 + q)
    rw [hcoef] at h
    simp (disch := omega) [if_neg] at h
    exact h
  have c111 : x 1 1 1 = 0 := by
    have h := hc (1 + q + q ^ 2)
    rw [hcoef] at h
    simp (disch := omega) [if_neg] at h
    exact h
  intro i j k hijk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hijk ⊢ <;> assumption

section Norm

variable [Fintype K] [Fintype F]

theorem pow_card_eq_self_iff (x : F) :
    x ^ Fintype.card K = x ↔ x ∈ Set.range (algebraMap K F) :=
  TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap x

theorem nrm_mem_range (hF : Fintype.card F = Fintype.card K ^ 3) (μ : F) :
    μ ^ (1 + Fintype.card K + Fintype.card K ^ 2) ∈ Set.range (algebraMap K F) := by
  rw [← pow_card_eq_self_iff]
  set q := Fintype.card K with hq
  have h3 : μ ^ (q ^ 3) = μ := by rw [← hF]; exact FiniteField.pow_card μ
  calc (μ ^ (1 + q + q ^ 2)) ^ q = μ ^ ((1 + q + q ^ 2) * q) := by rw [← pow_mul]
    _ = μ ^ (q + q ^ 2) * μ ^ (q ^ 3) := by rw [← pow_add]; congr 1; ring
    _ = μ ^ (1 + q + q ^ 2) := by rw [h3, ← pow_succ]; congr 1; ring

theorem exists_nrm_eq (hF : Fintype.card F = Fintype.card K ^ 3) (hq : 2 ≤ Fintype.card K)
    (κ : K) (hκ : κ ≠ 0) :
    ∃ μ : F, μ ≠ 0 ∧ algebraMap K F κ = μ ^ (1 + Fintype.card K + Fintype.card K ^ 2) := by
  obtain ⟨μ, hμ⟩ := FiniteField.norm_surjective (K := K) (K' := F) κ
  have hexp : (Nat.card F - 1) / (Nat.card K - 1) = 1 + Fintype.card K + Fintype.card K ^ 2 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hF]
    set q := Fintype.card K
    have hq1 : 0 < q - 1 := by omega
    apply Nat.div_eq_of_eq_mul_left hq1
    have : q ^ 3 - 1 = (1 + q + q ^ 2) * (q - 1) := by
      have hq' : 1 ≤ q := by omega
      zify [hq', Nat.one_le_pow 3 q (by omega)]
      ring
    exact this
  refine ⟨μ, ?_, ?_⟩
  · rintro rfl
    apply hκ
    have := FiniteField.algebraMap_norm_eq_pow (K := K) (K' := F) (x := (0 : F))
    rw [hμ, hexp, zero_pow (by omega)] at this
    exact (algebraMap K F).injective (by rw [this, map_zero])
  · have h := FiniteField.algebraMap_norm_eq_pow (K := K) (K' := F) (x := μ)
    rw [hμ, hexp] at h
    exact h

end Norm

section Gal

variable [Fintype K] [Finite F]

theorem aut_pow_three (hdeg : Module.finrank K F = 3) (σ : F ≃+* F)
    (hσ : ∀ c : K, σ (algebraMap K F c) = algebraMap K F c) : σ ^ 3 = 1 := by
  haveI : Module.Finite K F := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  let σ' : F ≃ₐ[K] F := AlgEquiv.ofRingEquiv hσ
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K F).2 σ'
  have hord : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic K F) = 3 := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hdeg]
  have h3 : (FiniteField.frobeniusAlgEquivOfAlgebraic K F) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have h4 : σ' ^ 3 = 1 := by
    rw [← hn]
    show (FiniteField.frobeniusAlgEquivOfAlgebraic K F ^ n.1) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  refine RingEquiv.ext fun x => ?_
  have := AlgEquiv.congr_fun h4 x
  have e : ∀ y, σ' y = σ y := fun y => rfl
  simpa [pow_succ, e] using this

end Gal

end D3

@[expose] def D3ModuleStatement : Prop :=
  ∀ (K F : Type) [Field K] [Fintype K] [CharP K 2] [Field F] [Finite F] [Algebra K F],
    Nat.card F = Nat.card K ^ 3 → 4 ≤ Nat.card K →
    ∀ (E : Type) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
      (B : LinearMap.BilinForm K E) (Qf : E → K),
      (∀ e, B e e = 0) → (∀ e, (∀ f, B e f = 0) → e = 0) →
      (∀ e f, Qf (e + f) = Qf e + Qf f + B e f) → (∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e) →
      (∃ S₁ S₂ : Submodule K E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, Qf x = 0) ∧
        ∀ x ∈ S₂, Qf x = 0) →
      Module.finrank K E = 8 →
      ∀ ρ : SL(2, F) →* (E ≃ₗ[K] E),
        (∀ g e, Qf (ρ g e) = Qf e) → Function.Injective ρ →
        ((∀ u v : E, (∀ g, ρ g u = u) → (∀ g, ρ g v = v) → B u v = 0) →
          ∀ e : E, (∀ g, ρ g e = e) → e = 0) →
        ∃ (σ : F ≃+* F) (θ : E ≃ₗ[K] D3.kForm (FiniteField.frobeniusAlgHom K F)),
          (∀ g e, (θ (ρ g e) : D3.Hyp F) = D3.act (FiniteField.frobeniusAlgHom K F : F →+* F)
            ((D2.slMap σ g : SL(2, F)) : Mat2 F) (θ e : D3.Hyp F)) ∧
          ∀ e, algebraMap K F (Qf e) = D3.quad (θ e : D3.Hyp F)

end

section

open Matrix
open scoped MatrixGroups

namespace D3

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[expose] def pt (τ : F →+* F) (w : Fin 2 → F) : Hyp F := fun i j k =>
  w i * τ (w j) * τ (τ (w k))

theorem pt_mem_kForm (τ : F →ₐ[K] F) (hτ : ∀ a, τ (τ (τ a)) = a) (w : Fin 2 → F) :
    pt (τ : F →+* F) w ∈ kForm τ := by
  intro i j k
  simp only [pt, map_mul, AlgHom.coe_toRingHom, hτ]
  ring

theorem act_pt (τ : F →+* F) (g : Mat2 F) (w : Fin 2 → F) :
    act τ g (pt τ w) = pt τ (g.mulVec w) := by
  funext i j k
  simp only [act, pt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul]
  ring

theorem polar_pt (τ : F →+* F) (v w : Fin 2 → F) :
    polar (pt τ v) (pt τ w) = (v 0 * w 1 + v 1 * w 0) * τ (v 0 * w 1 + v 1 * w 0) *
      τ (τ (v 0 * w 1 + v 1 * w 0)) := by
  simp only [polar, pt, map_add, map_mul]
  ring

theorem pt_ne_zero (τ : F →+* F) {w : Fin 2 → F} (hw : w ≠ 0) : pt τ w ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  intro h
  have := congrFun (congrFun (congrFun h i) i) i
  simp only [pt, Pi.zero_apply] at this
  exact mul_ne_zero (mul_ne_zero hi ((map_ne_zero τ).mpr hi))
    ((map_ne_zero τ).mpr ((map_ne_zero τ).mpr hi)) this

theorem pt_smul (τ : F →+* F) (s : F) (w : Fin 2 → F) :
    pt τ (s • w) = (s * τ s * τ (τ s)) • pt τ w := by
  funext i j k
  simp only [pt, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem e0_eq_pt (τ : F →+* F) : e0 F = pt τ (Pi.single 0 1) := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [e0, pt, Pi.single_apply]

section Fix

variable [Fintype K] [Fintype F]

theorem fix_U_line {q : ℕ} (hqK : Fintype.card K = q) (hq : 2 ≤ q) (hF : Fintype.card F = q ^ 3)
    (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ q) {x : Hyp F} (hx : x ∈ kForm τ)
    (hfix : ∀ a : F, act (τ : F →+* F) ((D2.uSL a : SL(2, F)) : Mat2 F) x = x) :
    ∃ c : K, x = (algebraMap K F c) • e0 F := by
  have h0 := coords_zero_of_fixed hq hF (τ : F →+* F) hτ x
    (fun a => by rw [hfix a])
  have hx000 : x 0 0 0 = τ (x 0 0 0) := hx 0 0 0
  have hpow : (x 0 0 0) ^ Fintype.card K = x 0 0 0 := by
    rw [hqK, ← hτ]
    exact hx000.symm
  obtain ⟨c, hc⟩ := (pow_card_eq_self_iff (K := K) (x 0 0 0)).mp hpow
  refine ⟨c, ?_⟩
  funext i j k
  by_cases hijk : i = 0 ∧ j = 0 ∧ k = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hijk
    simp [e0, hc]
  · simp [e0, hijk, h0 i j k hijk]

end Fix

end D3

end

end CFSG.RankThree.GF2n.Smith81
