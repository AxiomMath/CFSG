module

public import CFSG.Quasithin.AppendixH.H9.H93.A1Basic.A1Param
public import CFSG.Quasithin.AppendixH.H9.H93.A1Basic.A1Finite
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

theorem A1elt_single_zero : A1elt (Pi.single 0 1) = pairActN 4 gP01_23 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [A1elt_pairVec, A1_pairActN_gP01_23_pairVec]
  exact congrArg₂ pairVec (A1fst_snd_single_zero a b).1 (A1fst_snd_single_zero a b).2

theorem A1elt_single_one : A1elt (Pi.single 1 1) = pairActN 4 gP02_13 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [A1elt_pairVec, A1_pairActN_gP02_13_pairVec]
  exact congrArg₂ pairVec (A1fst_snd_single_one a b).1 (A1fst_snd_single_one a b).2

theorem A1elt_single_two : A1elt (Pi.single 2 1) = pairActN 4 gZJ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [A1elt_pairVec, A1_pairActN_gZJ_pairVec]
  exact congrArg₂ pairVec (A1fst_snd_single_two a b).1 (A1fst_snd_single_two a b).2

theorem A1elt_single_three : A1elt (Pi.single 3 1) = swapN 4 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [A1elt_pairVec, swapN_pairVec]
  exact congrArg₂ pairVec (A1fst_snd_single_three a b).1 (A1fst_snd_single_three a b).2

theorem A1elt_eq_prod (ε : Fin 4 → ZMod 2) :
    A1elt ε = A1elt (Pi.single 0 (ε 0)) * A1elt (Pi.single 1 (ε 1)) *
      A1elt (Pi.single 2 (ε 2)) * A1elt (Pi.single 3 (ε 3)) := by
  have h : ε = (Pi.single 0 (ε 0) : Fin 4 → ZMod 2) + (Pi.single 1 (ε 1) : Fin 4 → ZMod 2) +
      (Pi.single 2 (ε 2) : Fin 4 → ZMod 2) + (Pi.single 3 (ε 3) : Fin 4 → ZMod 2) := by
    funext i
    fin_cases i <;> simp
  rw [← A1elt_add, ← A1elt_add, ← A1elt_add, ← h]

theorem A1elt_single_mem {K : Subgroup (MulAut (PairN 4))} {i : Fin 4}
    (hi : A1elt (Pi.single i 1) ∈ K) (c : ZMod 2) : A1elt (Pi.single i c) ∈ K := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [Pi.single_zero, A1elt_zero]
    exact K.one_mem
  · exact hi

theorem A1elt_mem_of_gen {K : Subgroup (MulAut (PairN 4))}
    (h0 : A1elt (Pi.single 0 1) ∈ K) (h1 : A1elt (Pi.single 1 1) ∈ K)
    (h2 : A1elt (Pi.single 2 1) ∈ K) (h3 : A1elt (Pi.single 3 1) ∈ K) (ε : Fin 4 → ZMod 2) :
    A1elt ε ∈ K := by
  rw [A1elt_eq_prod]
  exact K.mul_mem (K.mul_mem (K.mul_mem (A1elt_single_mem h0 _) (A1elt_single_mem h1 _))
    (A1elt_single_mem h2 _)) (A1elt_single_mem h3 _)

theorem A1elt_mem_of_swap_zero {K : Subgroup (MulAut (PairN 4))}
    (h0 : A1elt (Pi.single 0 1) ∈ K) (h1 : A1elt (Pi.single 1 1) ∈ K)
    (h2 : A1elt (Pi.single 2 1) ∈ K) (ε : Fin 4 → ZMod 2) (h3 : ε 3 = 0) : A1elt ε ∈ K := by
  rw [A1elt_eq_prod, h3, Pi.single_zero, A1elt_zero, mul_one]
  exact K.mul_mem (K.mul_mem (A1elt_single_mem h0 _) (A1elt_single_mem h1 _))
    (A1elt_single_mem h2 _)

theorem A1hom_range : A1hom.range = A1g := by
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    show A1elt (Multiplicative.toAdd e) ∈ A1g
    refine A1elt_mem_of_gen ?_ ?_ ?_ ?_ _
    · rw [A1elt_single_zero]
      exact Subgroup.subset_closure (by simp)
    · rw [A1elt_single_one]
      exact Subgroup.subset_closure (by simp)
    · rw [A1elt_single_two]
      exact Subgroup.subset_closure (by simp)
    · rw [A1elt_single_three]
      exact Subgroup.subset_closure (by simp)
  · rw [A1g, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨Multiplicative.ofAdd (Pi.single 0 1), A1elt_single_zero⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 1 1), A1elt_single_one⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 2 1), A1elt_single_two⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 3 1), A1elt_single_three⟩

theorem A1hom_injective : Function.Injective A1hom := by
  rw [injective_iff_map_eq_one]
  intro e he
  have h : ∀ a b : Fin 4 → ZMod 2, A1fst (Multiplicative.toAdd e) a b = a ∧
      A1snd (Multiplicative.toAdd e) a b = b := by
    intro a b
    have h1 := congrArg (fun g : MulAut (PairN 4) => g (pairVec a b)) he
    exact pairVec_inj.mp h1
  exact Multiplicative.toAdd.injective (A1_eq_zero_of_fst_snd_eq _ h)

theorem A1hom_mem_Lg_iff (ε : Fin 4 → ZMod 2) :
    A1hom (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0 := by
  constructor
  · intro h
    by_contra h3
    obtain ⟨A, hA⟩ := mem_Lg_iff.mp h
    have h1 := congrArg (fun g : MulAut (PairN 4) => g (pairVec (Pi.single 0 1) 0)) hA
    rw [pairActN_pairVec, Matrix.mulVec_zero, A1hom_apply_pairVec] at h1
    have h2 := (pairVec_inj.mp h1).2
    rw [A1snd, if_neg h3] at h2
    exact A1vec_single_zero_ne_zero ε h2.symm
  · intro h3
    refine A1elt_mem_of_swap_zero ?_ ?_ ?_ ε h3
    · rw [A1elt_single_zero]
      exact pairActN_mem_Lg _
    · rw [A1elt_single_one]
      exact pairActN_mem_Lg _
    · rw [A1elt_single_two]
      exact pairActN_mem_Lg _

end CFSG.ASVolI.ChH
