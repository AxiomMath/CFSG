module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG

namespace FiveTransitive.ElevenElementaryAutNineFree

theorem nine_not_dvd_card
    (Q : Type*) [Group Q] [Finite Q] (hcomm : IsMulCommutative Q)
    (hp : ∀ q : Q, q ^ 11 = 1) (hcard : Nat.card Q ≤ 1331) :
    ¬ 9 ∣ Nat.card (MulAut Q) := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ := hcomm
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  let A := Additive Q
  have hAcard : Nat.card A ≤ 1331 := by
    rw [Nat.card_congr (Additive.toMul : Additive Q ≃ Q)]
    exact hcard
  have hsmul (a : A) : 11 • a = 0 := by
    change (a.toMul : Q) ^ 11 = 1
    exact hp a.toMul
  let _ : Module (ZMod 11) A := AddCommGroup.zmodModule hsmul
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 11) (V := A)
  rw [Nat.card_zmod] at hpow
  have hdim : Module.finrank (ZMod 11) A ≤ 3 := by
    by_contra hn
    have hb : 11 ^ 4 ≤ 11 ^ Module.finrank (ZMod 11) A :=
      pow_le_pow_right' (by norm_num) (show 4 ≤ Module.finrank (ZMod 11) A by omega)
    norm_num at hb
    omega
  let b := Module.finBasis (ZMod 11) A
  let autLinear : MulAut Q ≃* (A ≃ₗ[ZMod 11] A) :=
    { toFun := fun f => (MulEquiv.toAdditive f).toLinearEquiv
        (ZMod.map_smul (MulEquiv.toAdditive f))
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun f g => by ext x; rfl }
  let e := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 11) A).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)
  rw [Nat.card_congr e.toEquiv]
  have hsmall (d : ℕ) (hd : d ≤ 3) :
      ¬ 9 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 11)) := by
    interval_cases d <;> rw [Matrix.card_GL_field] <;> decide
  exact hsmall _ hdim

end FiveTransitive.ElevenElementaryAutNineFree

end CFSG
