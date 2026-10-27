module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open Matrix

variable {p : ℕ} [hp : Fact p.Prime]

@[expose] def ruAddAutEquivLinear (V : Type*) [AddCommGroup V] [Module (ZMod p) V] :
    Multiplicative (AddAut V) ≃* (V ≃ₗ[ZMod p] V) where
  toFun a := (Multiplicative.toAdd a).toLinearEquiv fun c x =>
    ZMod.map_smul (Multiplicative.toAdd a) c x
  invFun f := Multiplicative.ofAdd f.toAddEquiv
  left_inv _ := rfl
  right_inv f := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

@[expose] def ruMulAutEquivGL (n : ℕ) :
    MulAut (Multiplicative (Fin n → ZMod p)) ≃* GL (Fin n) (ZMod p) :=
  ((MulAutMultiplicative (Fin n → ZMod p)).trans
    (ruAddAutEquivLinear (p := p) (Fin n → ZMod p))).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n → ZMod p)).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm)

variable {W : Type*} [Group W]

theorem ru_nonempty_mulEquiv_of_elementary [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hpow : ∀ a : W, a ^ p = 1) {n : ℕ} (hcard : Nat.card W = p ^ n) :
    Nonempty (W ≃* Multiplicative (Fin n → ZMod p)) := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let _ : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule (n := p) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  have hF : Module.Finite (ZMod p) (Additive W) := Module.Finite.of_finite
  have hFr : Module.Free (ZMod p) (Additive W) := Module.Free.of_divisionRing _ _
  have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive W) _ _ _ hF
  have hfin : Module.finrank (ZMod p) (Additive W) =
      Module.finrank (ZMod p) (Fin n → ZMod p) := by
    rw [Nat.card_zmod] at h
    rw [Module.finrank_fin_fun]
    exact Nat.pow_right_injective hp.out.two_le (h.symm.trans hcard)
  exact ⟨AddEquiv.toMultiplicativeRight
    (@LinearEquiv.ofFinrankEq (ZMod p) (Additive W) (Fin n → ZMod p) _ _ _ hFr _ _ _ _ hF _
      hfin).toAddEquiv⟩

theorem ru_card_mulAut_elementary [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hpow : ∀ a : W, a ^ p = 1) {n : ℕ} (hcard : Nat.card W = p ^ n) :
    Nat.card (MulAut W) = ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
  obtain ⟨e⟩ := ru_nonempty_mulEquiv_of_elementary hcomm hpow hcard
  rw [Nat.card_congr ((MulAut.congr e).trans (ruMulAutEquivGL n)).toEquiv, Matrix.card_GL_field,
    ZMod.card]

theorem ru_card_mulAut_eight [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hpow : ∀ a : W, a ^ 2 = 1) (hcard : Nat.card W = 8) : Nat.card (MulAut W) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ru_card_mulAut_elementary hcomm hpow (n := 3) (by rw [hcard]; norm_num)]
  simp [Fin.prod_univ_succ]

end CFSG.Sporadic.RuSchreier
