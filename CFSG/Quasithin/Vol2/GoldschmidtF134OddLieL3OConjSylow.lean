module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OTorusDef
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem card_SL_three {K : Type} [Field K] [Finite K] :
    Nat.card SL(3, K) = Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  rw [LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3)]
  have h : (Finset.Icc 2 3 : Finset ℕ) = {2, 3} := by decide
  rw [h, Finset.prod_pair (by norm_num)]

theorem card_SL_three_eq {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = (q - 1) ^ 2 * (q ^ 3 * ((q + 1) * (q ^ 2 + q + 1))) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h2 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h3 : (r + 1) ^ 3 - 1 = r * (r ^ 2 + 3 * r + 3) := Nat.sub_eq_of_eq_add (by ring)
  rw [h2, h3, Nat.add_sub_cancel]
  ring

theorem not_dvd_card_SL_three_cofactor {p q : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) : ¬ p ∣ q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) := by
  intro h
  have h1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 hpq
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  have h2 := (ZMod.natCast_eq_zero_iff _ p).2 h
  push_cast at h2
  rw [h1] at h2
  norm_num at h2
  have h6 : ((6 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at h6
  have h7 : p ∣ 2 * 3 := h6
  rcases (Nat.Prime.dvd_mul hp.out).1 h7 with h8 | h8
  · have := Nat.le_of_dvd (by norm_num) h8
    omega
  · have := Nat.le_of_dvd (by norm_num) h8
    omega

section Torus

variable {K : Type} [Field K]

theorem card_units_prod : Nat.card (Kˣ × Kˣ) = (Nat.card K - 1) ^ 2 := by
  rw [Nat.card_prod, Nat.card_units, sq]

theorem injective_diagHom : Function.Injective (diagHom : Kˣ × Kˣ →* SL(3, K)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := congrArg (fun z : SL(3, K) => (z : Matrix (Fin 3) (Fin 3) K)) hx
  simp only [coe_diagHom, Matrix.SpecialLinearGroup.coe_one] at h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  simp [diagMat] at h0 h1
  exact Prod.ext h0 h1

variable [Finite K]

theorem exists_sylow_le_range_diagHom {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    ∃ S : Sylow p SL(3, K), (S : Subgroup SL(3, K)) ≤ (diagHom : Kˣ × Kˣ →* SL(3, K)).range := by
  obtain ⟨Y⟩ : Nonempty (Sylow p (Kˣ × Kˣ)) := inferInstance
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hcard : Nat.card ((Y : Subgroup (Kˣ × Kˣ)).map diagHom) =
      p ^ (Nat.card SL(3, K)).factorization p := by
    rw [Subgroup.card_map_of_injective injective_diagHom, Sylow.card_eq_multiplicity,
      card_units_prod, card_SL_three, card_SL_three_eq hq]
    have h1 : (Nat.card K - 1) ^ 2 ≠ 0 := by
      have := Finite.one_lt_card (α := K)
      exact pow_ne_zero 2 (by omega)
    have h2 : Nat.card K ^ 3 * ((Nat.card K + 1) * (Nat.card K ^ 2 + Nat.card K + 1)) ≠ 0 := by
      positivity
    rw [Nat.factorization_mul h1 h2, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_SL_three_cofactor hp5 hq hpq), add_zero]
  exact ⟨Sylow.ofCard _ hcard, Subgroup.map_le_range _ _⟩

end Torus

end CFSG.Quasithin.H13.NQCore.L3Odd
