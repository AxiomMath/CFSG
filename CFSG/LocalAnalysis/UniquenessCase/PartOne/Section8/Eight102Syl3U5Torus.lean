module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Torus
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open

variable {K : Type} [Field K]

private theorem torusPow_three_inf_hypScalars (h : UnitaryFieldData 2 2 K) :
    torusPow h 2 1 3 ⊓ hypScalars h 2 1 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨a, ha, hxmat⟩ := mem_torusPow.mp hx.1
  obtain ⟨c, hc, hcn, hxscalar⟩ := mem_normOneScalars.mp hx.2
  have hc1 : c = 1 := by
    have h1 : ((GeneralLinearGroup.scalar (HypIndex 2 1) c : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by
      rw [← hxscalar, hxmat]
      simp [torusEntries]
    simpa [GeneralLinearGroup.coe_scalar] using h1
  have hxgl : ((x : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = 1 := by
    rw [hxscalar, hc1]
    simp
  exact Subtype.ext (Units.ext hxgl)

private theorem hypProj_injOn_torusPow_three (h : UnitaryFieldData 2 2 K) :
    Set.InjOn (fun g : hypSU h 2 1 => hypProj h 2 1 g)
      (torusPow h 2 1 3 : Set (hypSU h 2 1)) := by
  intro g hg g' hg' heq
  have hker : g⁻¹ * g' ∈ (hypProj h 2 1).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    dsimp only at heq
    rw [heq, inv_mul_cancel]
  rw [ker_hypProj] at hker
  have hmemT : g⁻¹ * g' ∈ torusPow h 2 1 3 :=
    (torusPow h 2 1 3).mul_mem ((torusPow h 2 1 3).inv_mem hg) hg'
  have hmem : g⁻¹ * g' ∈ torusPow h 2 1 3 ⊓ hypScalars h 2 1 :=
    Subgroup.mem_inf.mpr ⟨hmemT, hker⟩
  rw [torusPow_three_inf_hypScalars h, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

private theorem card_map_torusPow_three (h : UnitaryFieldData 2 2 K) :
    Nat.card ((torusPow h 2 1 3).map (hypProj h 2 1)) = 9 := by
  have hmap : Nat.card ((torusPow h 2 1 3).map (hypProj h 2 1)) =
      Nat.card (torusPow h 2 1 3) :=
    Nat.card_image_of_injOn (hypProj_injOn_torusPow_three h)
  have hT : Nat.card (torusPow h 2 1 3) = 3 ^ 2 := by
    simpa using card_torusPow h 2 1 (m := 3) (by norm_num)
  rw [hmap, hT]
  norm_num

private theorem card_hypSU_two_one (h : UnitaryFieldData 2 2 K) :
    Nat.card (hypSU h 2 1) = 4 ^ 10 * 254840625 := by
  have hprod : (∏ i ∈ Finset.Icc 2 5,
      (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i)) = (254840625 : ℤ) := by decide
  have hSU := (card_hypSU h (r := 2) (ε := 1) (by norm_num)).1
  rw [hprod] at hSU
  have h' : (Nat.card (hypSU h 2 1) : ℤ) = ((4 ^ 10 * 254840625 : ℕ) : ℤ) := by
    rw [hSU]
    norm_num
  exact_mod_cast h'

private theorem card_hypScalars_two_one (h : UnitaryFieldData 2 2 K) :
    Nat.card (hypScalars h 2 1) = 5 := by
  have h := card_hypScalars h (r := 2) (ε := 1) (by norm_num)
  norm_num at h
  exact h

private theorem factorization_hypPSU_two_one (h : UnitaryFieldData 2 2 K) :
    (Nat.card (hypPSU h 2 1)).factorization 3 = 2 := by
  have hA := card_hypSU_two_one h
  have hB := card_hypScalars_two_one h
  have hCB := card_hypPSU_mul h (r := 2) (ε := 1)
  have hA9 : Nat.card (hypSU h 2 1) = 9 * (4 ^ 10 * 28315625) := by
    rw [hA]
    norm_num
  have hC5 : Nat.card (hypPSU h 2 1) * 5 = 9 * (4 ^ 10 * 28315625) := by
    rw [← hB, hCB, hA9]
  have hCne : Nat.card (hypPSU h 2 1) ≠ 0 := Nat.card_pos.ne'
  have hMne : 4 ^ 10 * 28315625 ≠ 0 := by norm_num
  have hM : ¬ 3 ∣ 4 ^ 10 * 28315625 :=
    Nat.Prime.not_dvd_mul Nat.prime_three (by norm_num) (by norm_num)
  have h := congrArg (fun n : ℕ => n.factorization 3) hC5
  rw [Nat.factorization_mul hCne (by norm_num : (5 : ℕ) ≠ 0),
      Nat.factorization_mul (by norm_num : (9 : ℕ) ≠ 0) hMne] at h
  simp only [Finsupp.add_apply] at h
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 5),
      Nat.factorization_eq_zero_of_not_dvd hM, add_zero, add_zero] at h
  have h9 : (9 : ℕ).factorization 3 = 2 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.factorization_pow_self (p := 3) (n := 2) Nat.prime_three
  rw [h9] at h
  simpa using h

theorem sylow_three_hypPSU_two_one (h : UnitaryFieldData 2 2 K) :
    IsPGroup 3 ((torusPow h 2 1 3).map (hypProj h 2 1)) ∧
      ¬ 3 ∣ ((torusPow h 2 1 3).map (hypProj h 2 1)).index ∧
      IsElemAbelian 3 ((torusPow h 2 1 3).map (hypProj h 2 1)) ∧
      Nat.card ((torusPow h 2 1 3).map (hypProj h 2 1)) = 9 := by
  have hcard := card_map_torusPow_three h
  have hfac : Nat.card ((torusPow h 2 1 3).map (hypProj h 2 1)) =
      3 ^ (Nat.card (hypPSU h 2 1)).factorization 3 := by
    rw [hcard, factorization_hypPSU_two_one h]
    norm_num
  have hcomm : IsMulCommutative ((torusPow h 2 1 3).map (hypProj h 2 1)) := by
    have hTcomm : IsMulCommutative (torusPow h 2 1 3) := (isElemAbelian_torusPow h 2 1 3).1
    have hTmul : ∀ a ∈ torusPow h 2 1 3, ∀ b ∈ torusPow h 2 1 3, a * b = b * a :=
      isMulCommutative_iff_of_setLike.mp hTcomm
    refine IsMulCommutative.of_setLike_mul_comm ?_
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    simpa only [map_mul] using congrArg (hypProj h 2 1) (hTmul a ha b hb)
  have hpow3 : ∀ x ∈ (torusPow h 2 1 3).map (hypProj h 2 1), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, pow_eq_one_of_mem_torusPow ht, map_one]
  refine ⟨?_, ?_, ⟨hcomm, hpow3⟩, hcard⟩
  · exact IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  · simpa only [Sylow.coe_ofCard] using (Sylow.ofCard _ hfac).not_dvd_index

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
