module

public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

private theorem l02qfno_ringEquiv_eq_one_of_card_prime {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (h : Nat.card F = p) (σ : F ≃+* F) : σ = 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card]; exact h
  let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F Fact.out hc
  have hcomp : σ.toRingHom.comp e.toRingHom = e.toRingHom := RingHom.ext_zmod _ _
  ext a
  obtain ⟨n, rfl⟩ := e.surjective a
  have := congrArg (fun f : ZMod p →+* F => f n) hcomp
  simpa [RingHom.comp_apply] using this

private theorem l02qfno_subsingleton_ringEquiv_of_card_le_three {F : Type} [Field F] [Finite F]
    (h : Nat.card F ≤ 3) : Subsingleton (F ≃+* F) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Nontrivial F := inferInstance
  have hmin : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hcases : Nat.card F = 2 ∨ Nat.card F = 3 := by omega
  rcases hcases with h2 | h3
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨fun σ τ => by
      rw [l02qfno_ringEquiv_eq_one_of_card_prime h2 σ,
        l02qfno_ringEquiv_eq_one_of_card_prime h2 τ]⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨fun σ τ => by
      rw [l02qfno_ringEquiv_eq_one_of_card_prime h3 σ,
        l02qfno_ringEquiv_eq_one_of_card_prime h3 τ]⟩

theorem fniLin_not_inner {m : ℕ} (hm : 2 ≤ m) {D : Type} [Field D] [Finite D] {τ : D ≃+* D}
    (hτ : τ ≠ 1) (B A : GL (Fin m) D) :
    ¬ ∀ x : LinearFlag.projectiveSL m D,
      LinearFlag.conjAut m D B (LinearFlag.fieldAut m D τ x) = LinearFlag.conjAut m D A x := by
  intro h
  have hcomp : LinearFlag.conjAut m D B * LinearFlag.fieldAut m D τ =
      LinearFlag.conjAut m D A := by
    ext x
    exact h x
  have hone : LinearFlag.conjAut m D (A⁻¹ * B) * LinearFlag.fieldAut m D τ = 1 := by
    calc LinearFlag.conjAut m D (A⁻¹ * B) * LinearFlag.fieldAut m D τ
        = (LinearFlag.conjAut m D A)⁻¹ *
            (LinearFlag.conjAut m D B * LinearFlag.fieldAut m D τ) := by
          rw [map_mul, map_inv]
          group
      _ = 1 := by rw [hcomp, inv_mul_cancel]
  by_cases hpar : 3 ≤ m ∨ 4 ≤ Nat.card D
  · obtain ⟨hτ1, -⟩ :=
      RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one' hm hpar (A⁻¹ * B) τ hone
    exact hτ hτ1
  · simp only [not_or, not_le] at hpar
    haveI : Subsingleton (D ≃+* D) :=
      l02qfno_subsingleton_ringEquiv_of_card_le_three (by omega)
    exact hτ (Subsingleton.elim τ 1)

end CFSG.StandardType
