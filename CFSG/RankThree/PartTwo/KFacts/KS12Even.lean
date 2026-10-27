module

import CFSG.Quasithin.Background.A318PC7
public import CFSG.RankThree.PartTwo.KFacts.KS12Moves
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section SL

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

@[expose] def glOfSqOne (M : Matrix (Fin 3) (Fin 3) K) (hM : M * M = 1) : GL (Fin 3) K :=
  ⟨M, M, hM, hM⟩

theorem glOfSqOne_sq (M : Matrix (Fin 3) (Fin 3) K) (hM : M * M = 1) :
    glOfSqOne M hM ^ 2 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, sq]; exact hM)

theorem exists_orderOf_two_slPi (hK : PiField π p f K) :
    ∃ x : slPi π 3 (p ^ f) K, orderOf x = 2 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.charP
  have hmem : ∀ (M : Matrix (Fin 3) (Fin 3) K) (hM : M * M = 1), M.det = 1 →
      (∀ h : UnitaryFieldData p f K, M.map h.bar = M) → Mᵀ = M →
      glOfSqOne M hM ∈ slPi π 3 (p ^ f) K := by
    intro M hM hdet hbar hT
    rw [mem_slPi_iff hπ]
    refine ⟨?_, hdet⟩
    cases π
    · have h := hπ rfl
      rw [mem_glPi_false h]
      change (M.map h.bar)ᵀ * M = 1
      rw [hbar h, hT, hM]
    · exact mem_glPi_true _ _
  by_cases hp2 : p = 2
  ·
    subst hp2
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hneg : (-1 : K) = 1 := by linear_combination -h2
    set M : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hMdef
    have hM : M * M = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hMdef, Matrix.mul_apply, Fin.sum_univ_three]
    have hdet : M.det = 1 := by
      rw [hMdef, det_fin_three]
      simp [hneg]
    have hbar : ∀ h : UnitaryFieldData 2 f K, M.map h.bar = M := fun h => by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hMdef]
    have hT : Mᵀ = M := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hMdef]
    refine ⟨⟨glOfSqOne M hM, hmem M hM hdet hbar hT⟩, orderOf_eq_prime ?_ ?_⟩
    · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact glOfSqOne_sq M hM)
    · intro h1
      have h := congrArg (fun u : slPi π 3 (2 ^ f) K =>
        ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
      simp [glOfSqOne, hMdef] at h
  ·
    have h2 : (2 : K) ≠ 0 := by
      intro h0
      have hp : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp hp)
    have hne : (-1 : K) ≠ 1 := by
      intro h
      apply h2
      linear_combination -h
    set M : Matrix (Fin 3) (Fin 3) K := !![-1, 0, 0; 0, -1, 0; 0, 0, 1] with hMdef
    have hM : M * M = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hMdef, Matrix.mul_apply, Fin.sum_univ_three]
    have hdet : M.det = 1 := by
      rw [hMdef, det_fin_three]
      simp
    have hodd : Odd (p ^ f) := Odd.pow (hK.prime.odd_of_ne_two hp2)
    have hbar : ∀ h : UnitaryFieldData p f K, M.map h.bar = M := fun h => by
      have hb : h.bar (-1) = -1 := by rw [h.bar_apply, hodd.neg_one_pow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hMdef, hb]
    have hT : Mᵀ = M := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hMdef]
    refine ⟨⟨glOfSqOne M hM, hmem M hM hdet hbar hT⟩, orderOf_eq_prime ?_ ?_⟩
    · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact glOfSqOne_sq M hM)
    · intro h1
      have h := congrArg (fun u : slPi π 3 (p ^ f) K =>
        ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
      simp [glOfSqOne, hMdef] at h
      exact hne h

end SL

theorem two_dvd_card_of_isSLThreePi {X : Type} [Group X] [Finite X] (hX : IsSLThreePi X) :
    2 ∣ Nat.card X := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨π, f, hK, ⟨e⟩⟩ : ∃ (π : Bool) (f : ℕ), PiField π (ringChar K) f K ∧
      Nonempty (X ≃* slPi π 3 (ringChar K ^ f) K) := by
    rcases hcase with ⟨hK, -, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
    · exact ⟨true, n, ⟨hp, n.2, hnc⟩, ⟨e⟩⟩
    · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, pow_zero] at hm
          rw [hm] at hq
          norm_num at hq
        · exact h0
      exact ⟨false, m, ⟨hp, hm1, by rw [hK, hm]; rfl⟩, ⟨hm ▸ e⟩⟩
  obtain ⟨x, hx⟩ := exists_orderOf_two_slPi hK
  rw [Nat.card_congr e.toEquiv]
  have : Finite (slPi π 3 (ringChar K ^ f) K) := Finite.of_equiv X e.toEquiv
  exact hx ▸ orderOf_dvd_natCard x

theorem two_dvd_card_M22 : 2 ∣ Nat.card Blueprint.NativeSporadic.M22 := by
  set a : Equiv.Perm (Fin 22) := List.formPerm [0, 12] * List.formPerm [1, 7] *
    List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] *
    List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13] with ha
  have haM : a ∈ Blueprint.NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)
  have ha2 : a ^ 2 = 1 := by rw [ha]; decide
  have ha1 : a ≠ 1 := by rw [ha]; decide
  have hord : orderOf (⟨a, haM⟩ : Blueprint.NativeSporadic.M22) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime ha2 ha1
  exact hord ▸ orderOf_dvd_natCard _

theorem two_dvd_card_of_isTripleCover {X : Type} [Group X] [Finite X] {Y : Type} [Group Y]
    (hX : Sec4.IsTripleCover X Y) (hY : 2 ∣ Nat.card Y) : 2 ∣ Nat.card X := by
  rw [card_of_isTripleCover hX]
  exact Dvd.dvd.mul_left hY 3

theorem two_dvd_card_alternatingGroup_six : 2 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem two_dvd_card_alternatingGroup_seven : 2 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem two_dvd_card_of_item122_type {X : Type} [Group X] [Finite X]
    (hX : IsSLThreePi X ∨ IsTripleCover X (alternatingGroup (Fin 6)) ∨
      IsTripleCover X (alternatingGroup (Fin 7)) ∨ IsTripleCover X Blueprint.NativeSporadic.M22) :
    2 ∣ Nat.card X := by
  rcases hX with h | h | h | h
  · exact two_dvd_card_of_isSLThreePi h
  · exact two_dvd_card_of_isTripleCover h two_dvd_card_alternatingGroup_six
  · exact two_dvd_card_of_isTripleCover h two_dvd_card_alternatingGroup_seven
  · exact two_dvd_card_of_isTripleCover h two_dvd_card_M22

theorem exists_orderOf_three_not_mem_center {X : Type*} [Group X] [Finite X]
    (hX : commutator X = ⊤) (hZ : Nat.card (Subgroup.center X) = 3) :
    ∃ x : X, orderOf x = 3 ∧ x ∉ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 (by rw [hZ])
  have hz3 : orderOf (z : X) = 3 := by rw [Subgroup.orderOf_coe, hz]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 X))
  have hSnc := not_isMulCommutative_sylow_of_perfect hX z.2 hz3 S
  by_contra hcon
  push Not at hcon
  have hcyc : IsCyclic (S : Subgroup X) :=
    CFSG.Quasithin.A318P.isCyclic_of_unique_three S.isPGroup' hZ fun r _ hr => hcon r hr
  exact hSnc ⟨⟨fun a b => (IsCyclic.commGroup.mul_comm a b)⟩⟩

end CFSG.RankThree.PartTwo.KFacts
