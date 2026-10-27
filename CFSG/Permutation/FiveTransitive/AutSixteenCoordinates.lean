module

public import CFSG.Permutation.FiveTransitive.AutSixteenPerfect
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG

namespace FiveTransitive.AutSixteenCoordinates

private theorem exists_mulEquiv
    (Q : Type*) [Group Q] [Finite Q] (hcard : Nat.card Q = 16)
    (hcomm : IsMulCommutative Q) (hp : ∀ q : Q, q ^ 2 = 1) :
    Nonempty (MulAut Q ≃* AutSixteenPerfect.GL4) := by
  classical
  let _ := hcomm
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  let A := Additive Q
  have hAcard : Nat.card A = 16 := by
    change Nat.card (Additive Q) = 16
    rw [Nat.card_congr (Additive.toMul : Additive Q ≃ Q), hcard]
  have htwo (a : A) : 2 • a = 0 := by
    change (a.toMul : Q) ^ 2 = 1
    exact hp a.toMul
  let _ : Module (ZMod 2) A := AddCommGroup.zmodModule htwo
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)
  rw [Nat.card_zmod, hAcard] at hpow
  have hfinrankLe : Module.finrank (ZMod 2) A ≤ 4 := by
    by_contra hnot
    have hfive : 5 ≤ Module.finrank (ZMod 2) A := by omega
    have hpows : 2 ^ 5 ≤ 2 ^ Module.finrank (ZMod 2) A :=
      pow_le_pow_right' (by norm_num) hfive
    omega
  have hfinrank : Module.finrank (ZMod 2) A = 4 := by
    interval_cases Module.finrank (ZMod 2) A <;> norm_num at hpow
    rfl
  let V := Fin 4 → ZMod 2
  have hVfinrank : Module.finrank (ZMod 2) V = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : A ≃ₗ[ZMod 2] V :=
    (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (hfinrank.trans hVfinrank.symm)).some
  let b : Module.Basis (Fin 4) (ZMod 2) A :=
    (Pi.basisFun (ZMod 2) (Fin 4)).map e.symm
  let autLinear : MulAut Q ≃* (A ≃ₗ[ZMod 2] A) := {
    toFun := fun f => (MulEquiv.toAdditive f).toLinearEquiv
      (ZMod.map_smul (MulEquiv.toAdditive f))
    invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
    left_inv := fun f => rfl
    right_inv := fun f => rfl
    map_mul' := fun f g => by ext x; rfl }
  exact ⟨autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) A).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)⟩

theorem perfect_and_card
    (Q : Type*) [Group Q] [Finite Q] (hcard : Nat.card Q = 16)
    (hcomm : IsMulCommutative Q) (hp : ∀ q : Q, q ^ 2 = 1) :
    Group.IsPerfect (MulAut Q) ∧ Nat.card (MulAut Q) = 20160 := by
  obtain ⟨e⟩ := exists_mulEquiv Q hcard hcomm hp
  let _ : Group.IsPerfect AutSixteenPerfect.GL4 := AutSixteenPerfect.perfect
  exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans AutSixteenPerfect.card⟩

end FiveTransitive.AutSixteenCoordinates

end CFSG
