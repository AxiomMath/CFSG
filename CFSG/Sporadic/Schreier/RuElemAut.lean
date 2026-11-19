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
  let : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let m : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule (n := p) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  let _ : Module (ZMod p) (Additive W) := m
  have hF : @Module.Finite (ZMod p) (Additive W) _ _ m := Module.Finite.of_finite
  have hFr : @Module.Free (ZMod p) (Additive W) _ _ m := Module.Free.of_divisionRing _ _
  have h : Nat.card (Additive W) =
      Nat.card (ZMod p) ^ @Module.finrank (ZMod p) (Additive W) _ _ m := by
    let b := @Module.Free.chooseBasis (ZMod p) (Additive W) _ _ m hFr
    have hb : @Finite (@Module.Free.ChooseBasisIndex (ZMod p) (Additive W) _ _ m hFr) :=
      @Module.Finite.finite_basis (ZMod p) (Additive W) _ _ m _ _ hF b
    have : Fintype (@Module.Free.ChooseBasisIndex (ZMod p) (Additive W) _ _ m hFr) :=
      @Fintype.ofFinite _ hb
    calc Nat.card (Additive W)
        = Nat.card (@Module.Free.ChooseBasisIndex (ZMod p) (Additive W) _ _ m hFr →₀ ZMod p) :=
          Nat.card_congr b.repr.toEquiv
      _ = Nat.card (@Module.Free.ChooseBasisIndex (ZMod p) (Additive W) _ _ m hFr → ZMod p) :=
          Nat.card_congr (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) _).toEquiv
      _ = Nat.card (ZMod p) ^
            Nat.card (@Module.Free.ChooseBasisIndex (ZMod p) (Additive W) _ _ m hFr) :=
          Nat.card_fun
      _ = Nat.card (ZMod p) ^ @Module.finrank (ZMod p) (Additive W) _ _ m := by
          rw [@Module.finrank_eq_card_basis (ZMod p) (Additive W) _ _ m _ _ _ b,
            Fintype.card_eq_nat_card]
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
