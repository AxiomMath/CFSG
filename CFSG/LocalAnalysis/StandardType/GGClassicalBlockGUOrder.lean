module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBUniCard
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Assembly Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
open CFSG.RankThree.PartOne.KCUnitaryModel

private lemma ggJSf3_GUFull_eq_primeFormUnitary {E : Type} [Field E] {m p f Q : ℕ}
    (h : UnitaryFieldData p f E) (hbar : ∀ x : E, h.bar x = x ^ Q) :
    GUFull m Q E = primeFormUnitary h (idGram E m) := by
  apply le_antisymm
  · rw [GUFull, Subgroup.closure_le]
    intro A hA
    rw [Set.mem_setOf_eq] at hA
    change A ∈ primeFormUnitary h (idGram E m)
    rw [mem_primeFormUnitary]
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) := by
      ext i j
      simp only [Matrix.map_apply, hbar]
    rw [hmap]
    simpa only [idGram, Units.val_one, Matrix.mul_one] using hA
  · intro A hA
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq]
    have hA' := (mem_primeFormUnitary.mp hA)
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) := by
      ext i j
      simp only [Matrix.map_apply, hbar]
    rw [idGram, Units.val_one, Matrix.mul_one] at hA'
    rwa [hmap] at hA'

private lemma ggJSf3_odd_pos {n : ℕ} (h : Odd n) : 0 < n := by
  rcases h with ⟨k, rfl⟩
  omega

private lemma ggJSf3_factorization_odd {n : ℕ} (h : Odd n) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h.not_two_dvd_nat

private lemma ggJSf3_odd_two_pow_sub_one {g j : ℕ} (hg : 1 ≤ g) (hj : 1 ≤ j) :
    Odd ((2 ^ g) ^ j - 1) := by
  rw [← ZMod.natCast_ne_zero_iff_odd]
  have hq : ((2 ^ g : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, ZMod.natCast_self 2, zero_pow (by omega : g ≠ 0)]
  have hqi : (((2 ^ g : ℕ) ^ j : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, hq, zero_pow (by omega : j ≠ 0)]
  have h1 : 1 ≤ (2 ^ g) ^ j :=
    Nat.one_le_pow j (2 ^ g) (Nat.one_le_pow g 2 (by norm_num))
  rw [Nat.cast_sub h1, hqi]
  norm_num

private lemma ggJSf3_odd_pow_add_one {g j : ℕ} (hg : 1 ≤ g) (hj : 1 ≤ j) :
    Odd ((2 ^ g) ^ j + 1) := by
  rw [← ZMod.natCast_ne_zero_iff_odd]
  have hq : ((2 ^ g : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, ZMod.natCast_self 2, zero_pow (by omega : g ≠ 0)]
  have hqi : (((2 ^ g : ℕ) ^ j : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, hq, zero_pow (by omega : j ≠ 0)]
  rw [Nat.cast_add, hqi]
  norm_num

private lemma ggJSf3_odd_uFactor {g i : ℕ} (hg : 1 ≤ g) (hi : 1 ≤ i) :
    Odd (uFactor (2 ^ g) i) := by
  unfold uFactor
  split_ifs with hev
  · exact ggJSf3_odd_two_pow_sub_one hg hi
  · exact ggJSf3_odd_pow_add_one hg hi

private lemma ggJSf3_prod_uFactor_ne_zero {m g : ℕ} (hg : 1 ≤ g) :
    (∏ i ∈ Finset.Icc 1 m, uFactor (2 ^ g) i) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  exact (ggJSf3_odd_pos (ggJSf3_odd_uFactor hg (Finset.mem_Icc.1 hi).1)).ne'

private lemma ggJSf3_sum_uFactor_factorization {m g : ℕ} (hg : 1 ≤ g) :
    (∑ i ∈ Finset.Icc 1 m, (uFactor (2 ^ g) i).factorization 2) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact ggJSf3_factorization_odd
    (ggJSf3_odd_uFactor hg (Finset.mem_Icc.1 hi).1)

private lemma ggJSf3_factorization_two_pow (g e : ℕ) :
    ((2 ^ g) ^ e).factorization 2 = g * e := by
  rw [← pow_mul, Nat.factorization_pow_self Nat.prime_two]

private lemma ggJSf3_one_le_of_card_eq_sq {E : Type} [Field E] [Fintype E] {g : ℕ}
    (hE : Fintype.card E = (2 ^ g) ^ 2) : 1 ≤ g := by
  by_contra hg
  have hg0 : g = 0 := by omega
  rw [hg0] at hE
  norm_num at hE
  have h2 : 1 < Fintype.card E := Fintype.one_lt_card
  omega

theorem factorization_two_card_GUFull {E : Type} [Field E] [Fintype E] {m g : ℕ}
    (hE : Fintype.card E = (2 ^ g) ^ 2) :
    (Nat.card ↥(GUFull m (2 ^ g) E)).factorization 2 = g * (m * (m - 1) / 2) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    haveI : Subsingleton (GL (Fin 0) E) := inferInstance
    have hcard : Nat.card ↥(GUFull 0 (2 ^ g) E) = 1 :=
      Nat.card_of_subsingleton ⟨1, (GUFull 0 (2 ^ g) E).one_mem⟩
    rw [hcard]
    simp
  · have hg : 1 ≤ g := ggJSf3_one_le_of_card_eq_sq hE
    let h : UnitaryFieldData 2 g E :=
      { prime := Nat.prime_two
        one_le := hg
        card := by
          rw [Nat.card_eq_fintype_card, hE]
          conv_lhs => rw [← pow_mul]
          rw [Nat.mul_comm] }
    have hbar : ∀ x : E, h.bar x = x ^ (2 ^ g) := by
      intro x
      rw [UnitaryFieldData.bar_apply]
    have hGU : GUFull m (2 ^ g) E = primeFormUnitary h (idGram E m) :=
      ggJSf3_GUFull_eq_primeFormUnitary h hbar
    have hnat : Nat.card ↥(primeFormUnitary h (idGram E m)) =
        (2 ^ g) ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 1 m, uFactor (2 ^ g) i := by
      have hint := card_primeFormUnitary_int h hm
      have h1 : ((Nat.card (primeFormUnitary h ((1 : GL (Fin m) E) :
          Matrix (Fin m) (Fin m) E)) : ℕ) : ℤ) =
          (((2 ^ g) ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 1 m,
            uFactor (2 ^ g) i : ℕ) : ℤ) := by
        rw [hint]
        push_cast
        congr 1
        exact Finset.prod_congr rfl fun i _ =>
          (cast_uFactor (Nat.one_le_pow g 2 (by norm_num)) i).symm
      have h1' : ((Nat.card (primeFormUnitary h (idGram E m)) : ℕ) : ℤ) =
          (((2 ^ g) ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 1 m,
            uFactor (2 ^ g) i : ℕ) : ℤ) := by
        simpa only [idGram] using h1
      exact_mod_cast h1'
    rw [hGU, hnat]
    have hpow : (2 ^ g) ^ (m * (m - 1) / 2) ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero g (by norm_num : (2 : ℕ) ≠ 0))
    have hne : ∀ i ∈ Finset.Icc 1 m, uFactor (2 ^ g) i ≠ 0 := by
      intro i hi
      exact (ggJSf3_odd_pos
        (ggJSf3_odd_uFactor hg (Finset.mem_Icc.1 hi).1)).ne'
    have hprod : (∏ i ∈ Finset.Icc 1 m, uFactor (2 ^ g) i) ≠ 0 :=
      ggJSf3_prod_uFactor_ne_zero hg
    rw [Nat.factorization_mul hpow hprod, Finsupp.add_apply,
      Nat.factorization_prod hne, Finsupp.coe_finset_sum, Finset.sum_apply]
    rw [ggJSf3_factorization_two_pow, ggJSf3_sum_uFactor_factorization hg]
    simp

end CFSG.StandardType.ClassicalBlocks
