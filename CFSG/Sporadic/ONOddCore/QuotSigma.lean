module

public import CFSG.Sporadic.ONOddCore.SigmaElem
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.OuterAutomorphisms
open Matrix

theorem F4_unit_pow : ∀ x : F4, x ≠ 0 → ∃ d < 3, F4.ω ^ d = x := by decide

theorem det_dGL : ((dGL : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = F4.ω := by
  rw [dGL_mat, det_diagonal, Fin.prod_univ_three]
  decide

theorem det_GL_ne_zero (A : GL (Fin 3) F4) : ((A : Matrix (Fin 3) (Fin 3) F4)).det ≠ 0 :=
  (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit |>.ne_zero

theorem exists_SL_mul_dGL_pow (A : GL (Fin 3) F4) :
    ∃ d < 3, ∃ B : SpecialLinearGroup (Fin 3) F4, A = SpecialLinearGroup.toGL B * dGL ^ d := by
  obtain ⟨d, hd, hdet⟩ := F4_unit_pow _ (det_GL_ne_zero A)
  set C : GL (Fin 3) F4 := A * (dGL ^ d)⁻¹ with hC
  have hCdet : ((C : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    have h1 : ((A : Matrix (Fin 3) (Fin 3) F4)).det =
        ((C : Matrix (Fin 3) (Fin 3) F4)).det * F4.ω ^ d := by
      have e : A = C * dGL ^ d := by rw [hC, inv_mul_cancel_right]
      conv_lhs => rw [e]
      rw [Units.val_mul, det_mul, Units.val_pow_eq_pow_val, det_pow, det_dGL]
    rw [← hdet] at h1
    have hω : F4.ω ^ d ≠ 0 := pow_ne_zero _ (by decide)
    exact (mul_eq_right₀ hω).1 h1.symm
  refine ⟨d, hd, ⟨C, hCdet⟩, ?_⟩
  have e : SpecialLinearGroup.toGL (⟨C, hCdet⟩ : SpecialLinearGroup (Fin 3) F4) = C :=
    Units.ext rfl
  rw [e, hC, inv_mul_cancel_right]

theorem fieldAut_eq_pow (τ : F4 ≃+* F4) :
    ∃ f < 2, LinearFlag.fieldAut 3 F4 τ = LinearFlag.fieldAut 3 F4 frob ^ f := by
  rcases ringEquiv_eq τ with rfl | rfl
  · exact ⟨0, by norm_num, by rw [pow_zero]; exact map_one _⟩
  · exact ⟨1, by norm_num, (pow_one _).symm⟩

theorem exists_sigma
    (α : MulAut onX) :
    ∃ d < 3, ∃ f < 2, ∃ g < 2, ∃ x : onX, α = MulAut.conj x * sigmaX d f g := by
  set β : MulAut (LinearFlag.projectiveSL 3 F4) := (thetaX.trans α).trans thetaX.symm with hβdef
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := F4) (n := 3) (by norm_num)
  obtain ⟨A, τ, ε, hε, hβ⟩ := hgen β
  obtain ⟨d, hd, B, rfl⟩ := exists_SL_mul_dGL_pow A
  obtain ⟨f, hf, hτ⟩ := fieldAut_eq_pow τ
  have hβ' : β = MulAut.conj (LinearFlag.proj 3 F4 B) * gammaAut d f ε := by
    rw [hβ, map_mul, LinearFlag.conjAut_toGL, hτ, gammaAut]
    group
  refine ⟨d, hd, f, hf, ε, by omega, thetaX (LinearFlag.proj 3 F4 B), ?_⟩
  refine MulEquiv.ext fun y => ?_
  have hy : α y = thetaX (β (thetaX.symm y)) := by
    rw [hβdef]
    simp
  rw [hy, hβ', MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, MulAut.mul_apply,
    MulAut.conj_apply, sigmaX]
  rfl

@[expose] def xEquivS :
    onX ≃* S := thetaX.symm.trans theta

theorem card_mulAut_X :
    Nat.card (MulAut onX) = 241920 := by
  obtain ⟨e, -⟩ := full_automorphism_action
  rw [Nat.card_congr (MulAut.congr xEquivS).toEquiv, ← Nat.card_congr e.toEquiv, card_R]

theorem conj_injective_X :
    Function.Injective (MulAut.conj : onX →* MulAut onX) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hc : (x : Equiv.Perm (Fin 120)) ∈
      Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut onX => ((α ⟨y, hy⟩ : onX) : Equiv.Perm (Fin 120))) hx
    simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc y * x = x * y * (x : Equiv.Perm (Fin 120))⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [onX_centralizer, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem card_inner_X :
    Nat.card (OuterAutomorphisms.inner onX) = 20160 := by
  rw [OuterAutomorphisms.inner, ← Nat.card_congr (MonoidHom.ofInjective conj_injective_X).toEquiv,
    card_onX]

theorem card_outer_X :
    Nat.card (Outer onX) = 12 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (OuterAutomorphisms.inner onX)
  rw [card_mulAut_X, card_inner_X] at h
  have h' : Nat.card (Outer onX) * 20160 = 12 * 20160 := by
    rw [← h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

@[expose] def sigmaOuter
    (t : Fin 3 × Fin 2 × Fin 2) : Outer onX :=
  (sigmaX t.1 t.2.1 t.2.2 : Outer onX)

theorem sigmaOuter_surjective :
    Function.Surjective sigmaOuter := by
  intro c
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨d, hd, f, hf, g, hg, x, rfl⟩ := exists_sigma α
  refine ⟨(⟨d, hd⟩, ⟨f, hf⟩, ⟨g, hg⟩), ?_⟩
  rw [sigmaOuter]
  simp only
  have h1 : ((MulAut.conj x : MulAut onX) : Outer onX) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨x, rfl⟩)
  rw [QuotientGroup.mk_mul, h1, one_mul]

theorem sigmaOuter_bijective :
    Function.Bijective sigmaOuter :=
  sigmaOuter_surjective.bijective_of_nat_card_le (by rw [card_outer_X]; simp)

theorem sigmaX_outer_injective
    {d d' f f' g g' : ℕ} (hd : d < 3) (hd' : d' < 3) (hf : f < 2)
    (hf' : f' < 2) (hg : g < 2) (hg' : g' < 2)
    (h : (sigmaX d f g : Outer onX) = (sigmaX d' f' g' : Outer onX)) :
    d = d' ∧ f = f' ∧ g = g' := by
  have := sigmaOuter_bijective.1 (a₁ := (⟨d, hd⟩, ⟨f, hf⟩, ⟨g, hg⟩))
    (a₂ := (⟨d', hd'⟩, ⟨f', hf'⟩, ⟨g', hg'⟩)) h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  exact this

end CFSG.Sporadic.ONOddCore
