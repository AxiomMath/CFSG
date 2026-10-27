module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepDefs
public import Mathlib.RingTheory.Henselian

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L829NK

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.Quasithin.H.SL3Rep

theorem natCard_linearEquiv_prod (E W : Type) [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [Module.Finite E W] :
    Nat.card (W ≃ₗ[E] W) = ∏ i : Fin (Module.finrank E W),
      (Nat.card E ^ Module.finrank E W - Nat.card E ^ (i : ℕ)) := by
  have := Fintype.ofFinite E
  let e : (W ≃ₗ[E] W) ≃* Matrix.GeneralLinearGroup (Fin (Module.finrank E W)) E :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E W).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis E W)).toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, Nat.card_eq_fintype_card (α := E)]

theorem not_dvd_prod_of_lt_three (E : Type) [Field E] [Finite E]
    (hE : Nat.card E = 2 ∨ Nat.card E = 4) (d : ℕ) (hd : d < 3) :
    ¬ 168 ∣ ∏ i : Fin d, (Nat.card E ^ d - Nat.card E ^ (i : ℕ)) := by
  rcases hE with h | h <;> rw [h] <;> interval_cases d <;> norm_num [Fin.prod_univ_succ]

theorem nk_three_le_finrank {E W : Type} [Field E] [Finite E]
    (hE : Nat.card E = 2 ∨ Nat.card E = 4)
    [AddCommGroup W] [Module E W] [Module.Finite E W] (θ : GS →* (W ≃ₗ[E] W))
    (hinj : Function.Injective θ) : 3 ≤ Module.finrank E W := by
  by_contra hlt
  have hlt' : Module.finrank E W < 3 := by omega
  have hGS : Nat.card GS = 168 := natCard_linearEquiv finrank_V3
  have hdvd : Nat.card GS ∣ Nat.card (W ≃ₗ[E] W) := Subgroup.card_dvd_of_injective θ hinj
  rw [hGS, natCard_linearEquiv_prod E W] at hdvd
  exact not_dvd_prod_of_lt_three E hE _ hlt' hdvd

theorem nk_card_le_fixed_mul {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (r : U →ₗ[ZMod 2] U) (c : ℕ) (hc : Nat.card (LinearMap.range (r - LinearMap.id)) ≤ c) :
    Nat.card U ≤ Nat.card {u : U // r u = u} * c := by
  have hker : Nat.card (LinearMap.ker (r - LinearMap.id)) = Nat.card {u : U // r u = u} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hsplit : Nat.card U = Nat.card (LinearMap.ker (r - LinearMap.id)) *
      Nat.card (LinearMap.range (r - LinearMap.id)) := by
    rw [natCard_eq_two_pow U, natCard_eq_two_pow (LinearMap.ker (r - LinearMap.id)),
      natCard_eq_two_pow (LinearMap.range (r - LinearMap.id)), ← pow_add, add_comm,
      LinearMap.finrank_range_add_finrank_ker]
  rw [hsplit, ← hker]
  exact Nat.mul_le_mul (le_refl _) hc

end CFSG.Quasithin.H13.L829NK
