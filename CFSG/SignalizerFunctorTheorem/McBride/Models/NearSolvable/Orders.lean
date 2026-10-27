module

public import CFSG.Open.SignalizerFunctorDefs
import CFSG.Walter.PSL2Facts.Even
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Bridge
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace NearSolvable

theorem card_psl2_even {p : ℕ} (hp : p ≠ 0) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)) =
      2 ^ p * ((2 ^ p) ^ 2 - 1) :=
  CFSG.Walter.psl2_even_card hp

theorem card_psl2_three {p : ℕ} (hp : p ≠ 0) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) =
      3 ^ p * ((3 ^ p) ^ 2 - 1) / 2 := by
  have hK : Nat.card (GaloisField 3 p) = 3 ^ p := GaloisField.card 3 p hp
  have := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 p)
    ⟨3, p, Nat.prime_three, by decide, Nat.one_le_iff_ne_zero.mpr hp, hK⟩
  rw [hK] at this
  exact this

theorem card_sz (n : ℕ) :
    Nat.card (Sz n) =
      (2 ^ (2 * n + 1)) ^ 2 * ((2 ^ (2 * n + 1)) ^ 2 + 1) * (2 ^ (2 * n + 1) - 1) := by
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  rw [Nat.card_congr e.toEquiv,
    CFSG.LieType.Ree.suzuki_order (GaloisField.card 2 (2 * n + 1) (by omega))]
  ring

theorem card_psu3_mul_gcd {p : ℕ} (hp : 1 ≤ p) :
    Nat.card (PSU3 2 p) * Nat.gcd 3 (2 ^ p + 1) =
      (2 ^ p) ^ 3 * (((2 ^ p) ^ 2 - 1) * ((2 ^ p) ^ 3 + 1)) := by
  have h := unitaryFieldData_galoisField hp
  have hmul := card_hypPSU_mul h (r := 1) (ε := 1)
  have hZ := card_hypScalars h (r := 1) (ε := 1) (by omega)
  have hS := (card_hypSU h (r := 1) (ε := 1) (by omega)).1
  have h1 : 1 ≤ (2 ^ p) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  have hS' : Nat.card (hypSU h 1 1) =
      (2 ^ p) ^ 3 * (((2 ^ p) ^ 2 - 1) * ((2 ^ p) ^ 3 + 1)) := by
    have : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
    rw [this, Finset.prod_pair (by norm_num)] at hS
    have : ((Nat.card (hypSU h 1 1) : ℕ) : ℤ) =
        (((2 ^ p) ^ 3 * (((2 ^ p) ^ 2 - 1) * ((2 ^ p) ^ 3 + 1)) : ℕ) : ℤ) := by
      rw [hS]
      push_cast [Nat.cast_sub h1]
      norm_num
    exact_mod_cast this
  rw [← hS', ← hmul, Nat.card_congr (psu3EquivHypPSU hp).toEquiv, hZ]

theorem card_psu3 {p : ℕ} (hp : 1 ≤ p) :
    Nat.card (PSU3 2 p) =
      (2 ^ p) ^ 3 * (((2 ^ p) ^ 2 - 1) * ((2 ^ p) ^ 3 + 1)) / Nat.gcd 3 (2 ^ p + 1) := by
  rw [← card_psu3_mul_gcd hp, Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by norm_num))]

theorem card_psu3_of_odd {p : ℕ} (hp : Odd p) :
    Nat.card (PSU3 2 p) = (2 ^ p) ^ 3 * ((2 ^ p) ^ 3 + 1) * ((2 ^ p) ^ 2 - 1) / 3 := by
  have h3 : 3 ∣ 2 ^ p + 1 := by have := two_pow_mod_three hp; omega
  rw [card_psu3 hp.pos, Nat.gcd_eq_left h3]
  congr 1
  ring

end NearSolvable

open NearSolvable

theorem nearSimpleModel_card
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {S : Type*} [Group S]
    (hS : signalizerNearSimpleModel p S) :
    Nat.card S = 2 ^ p * ((2 ^ p) ^ 2 - 1) ∨ Nat.card S = 3 ^ p * ((3 ^ p) ^ 2 - 1) / 2 ∨
      Nat.card S = (2 ^ p) ^ 2 * ((2 ^ p) ^ 2 + 1) * (2 ^ p - 1) ∨
      Nat.card S = (2 ^ p) ^ 3 * ((2 ^ p) ^ 3 + 1) * ((2 ^ p) ^ 2 - 1) / 3 := by
  rcases hS with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv]
    exact card_psl2_even hp.ne_zero
  · right; left
    rw [Nat.card_congr e.toEquiv]
    exact card_psl2_three hp.ne_zero
  · right; right; left
    rw [Nat.card_congr e.toEquiv]
    exact card_sz n
  · right; right; right
    rw [Nat.card_congr e.toEquiv]
    exact card_psu3_of_odd (hp.odd_of_ne_two hodd)

end CFSG.SignalizerFunctorTheorem.McBride
