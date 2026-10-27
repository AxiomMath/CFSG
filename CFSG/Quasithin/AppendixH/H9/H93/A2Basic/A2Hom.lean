module

public import CFSG.Quasithin.AppendixH.H9.H93.A2Basic.A2Action
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

@[expose] def a2Fun (ε : Fin 4 → ZMod 2) (x : PairN 4) : PairN 4 :=
  pairVec (A2fst ε x.1.toAdd x.2.toAdd) (A2snd ε x.1.toAdd x.2.toAdd)

theorem a2Fun_pairVec (ε a b : Fin 4 → ZMod 2) :
    a2Fun ε (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b) := rfl

theorem A2fst_add (ε a b a' b' : Fin 4 → ZMod 2) :
    A2fst ε (a + a') (b + b') = A2fst ε a b + A2fst ε a' b' := by
  unfold A2fst
  split_ifs
  · exact A2vec_add_vec ε a a'
  · exact A2vec_add_vec ε b b'

theorem A2snd_add (ε a b a' b' : Fin 4 → ZMod 2) :
    A2snd ε (a + a') (b + b') = A2snd ε a b + A2snd ε a' b' := by
  unfold A2snd
  split_ifs
  · exact A2vec_add_vec ε b b'
  · exact A2vec_add_vec ε a a'

theorem A2fst_comp (ε ε' a b : Fin 4 → ZMod 2) :
    A2fst ε (A2fst ε' a b) (A2snd ε' a b) = A2fst (ε + ε') a b := by
  rcases zmod_two_cases (ε 3) with h3 | h3 <;> rcases zmod_two_cases (ε' 3) with h3' | h3' <;>
    simp [A2fst, A2snd, h3, h3', A2vec_add_eps, A2_one_add_one]

theorem A2snd_comp (ε ε' a b : Fin 4 → ZMod 2) :
    A2snd ε (A2fst ε' a b) (A2snd ε' a b) = A2snd (ε + ε') a b := by
  rcases zmod_two_cases (ε 3) with h3 | h3 <;> rcases zmod_two_cases (ε' 3) with h3' | h3' <;>
    simp [A2fst, A2snd, h3, h3', A2vec_add_eps, A2_one_add_one]

theorem A2fst_zero (a b : Fin 4 → ZMod 2) : A2fst 0 a b = a := by
  simp [A2fst, A2vec_zero_eps]

theorem A2snd_zero (a b : Fin 4 → ZMod 2) : A2snd 0 a b = b := by
  simp [A2snd, A2vec_zero_eps]

theorem a2Fun_mul (ε : Fin 4 → ZMod 2) (x y : PairN 4) :
    a2Fun ε (x * y) = a2Fun ε x * a2Fun ε y := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  obtain ⟨a', b', rfl⟩ := pairVec_surj y
  rw [pairVec_mul, a2Fun_pairVec, a2Fun_pairVec, a2Fun_pairVec, pairVec_mul, A2fst_add,
    A2snd_add]

theorem a2Fun_comp (ε ε' : Fin 4 → ZMod 2) (x : PairN 4) :
    a2Fun ε (a2Fun ε' x) = a2Fun (ε + ε') x := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [a2Fun_pairVec, a2Fun_pairVec, a2Fun_pairVec, A2fst_comp, A2snd_comp]

theorem a2Fun_zero (x : PairN 4) : a2Fun 0 x = x := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [a2Fun_pairVec, A2fst_zero, A2snd_zero]

theorem a2Fun_self (ε : Fin 4 → ZMod 2) (x : PairN 4) : a2Fun ε (a2Fun ε x) = x := by
  rw [a2Fun_comp, A2eps_add_self, a2Fun_zero]

@[expose] def a2Aut (ε : Fin 4 → ZMod 2) : MulAut (PairN 4) where
  toFun := a2Fun ε
  invFun := a2Fun ε
  left_inv := a2Fun_self ε
  right_inv := a2Fun_self ε
  map_mul' := a2Fun_mul ε

@[expose] def a2Hom : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4) where
  toFun ε := a2Aut ε.toAdd
  map_one' := MulEquiv.ext fun x => a2Fun_zero x
  map_mul' x y := MulEquiv.ext fun z => (a2Fun_comp x.toAdd y.toAdd z).symm

theorem a2Hom_apply (ε a b : Fin 4 → ZMod 2) :
    a2Hom (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b) := rfl

theorem A2_ker_check :
    ∀ ε : Fin 4 → ZMod 2, (∀ a : Fin 4 → ZMod 2, A2fst ε a 0 = a) → ε = 0 := by
  decide +kernel

theorem a2Hom_injective : Function.Injective a2Hom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨ε, rfl⟩ := Multiplicative.ofAdd.surjective x
  have h : ∀ a, A2fst ε a 0 = a := fun a => by
    have := congrArg (fun g : MulAut (PairN 4) => g (pairVec a 0)) hx
    exact (pairVec_inj.mp this).1
  rw [A2_ker_check ε h]
  rfl

theorem A2fst_single_zero : ∀ a b : Fin 4 → ZMod 2, A2fst (Pi.single 0 1) a b = vP01 a := by
  decide +kernel

theorem A2snd_single_zero : ∀ a b : Fin 4 → ZMod 2, A2snd (Pi.single 0 1) a b = vP01 b := by
  decide +kernel

theorem A2fst_single_one : ∀ a b : Fin 4 → ZMod 2, A2fst (Pi.single 1 1) a b = vP23 a := by
  decide +kernel

theorem A2snd_single_one : ∀ a b : Fin 4 → ZMod 2, A2snd (Pi.single 1 1) a b = vP23 b := by
  decide +kernel

theorem A2fst_single_two : ∀ a b : Fin 4 → ZMod 2, A2fst (Pi.single 2 1) a b = vZJ a := by
  decide +kernel

theorem A2snd_single_two : ∀ a b : Fin 4 → ZMod 2, A2snd (Pi.single 2 1) a b = vZJ b := by
  decide +kernel

theorem A2fst_single_three : ∀ a b : Fin 4 → ZMod 2, A2fst (Pi.single 3 1) a b = b := by
  decide +kernel

theorem A2snd_single_three : ∀ a b : Fin 4 → ZMod 2, A2snd (Pi.single 3 1) a b = a := by
  decide +kernel

theorem a2Hom_single_zero :
    a2Hom (Multiplicative.ofAdd (Pi.single 0 1)) = pairActN 4 gP01 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [a2Hom_apply, A2g_pairActN_gP01_pairVec, A2fst_single_zero, A2snd_single_zero]

theorem a2Hom_single_one :
    a2Hom (Multiplicative.ofAdd (Pi.single 1 1)) = pairActN 4 gP23 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [a2Hom_apply, A2g_pairActN_gP23_pairVec, A2fst_single_one, A2snd_single_one]

theorem a2Hom_single_two :
    a2Hom (Multiplicative.ofAdd (Pi.single 2 1)) = pairActN 4 gZJ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [a2Hom_apply, A2g_pairActN_gZJ_pairVec, A2fst_single_two, A2snd_single_two]

theorem a2Hom_single_three :
    a2Hom (Multiplicative.ofAdd (Pi.single 3 1)) = swapN 4 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [a2Hom_apply, swapN_pairVec, A2fst_single_three, A2snd_single_three]

theorem a2Hom_mem_of_gens {H : Subgroup (MulAut (PairN 4))} (ε : Fin 4 → ZMod 2)
    (h0 : ε 0 = 1 → pairActN 4 gP01 ∈ H) (h1 : ε 1 = 1 → pairActN 4 gP23 ∈ H)
    (h2 : ε 2 = 1 → pairActN 4 gZJ ∈ H) (h3 : ε 3 = 1 → swapN 4 ∈ H) :
    a2Hom (Multiplicative.ofAdd ε) ∈ H := by
  have hε : ε = (Pi.single 0 (ε 0) : Fin 4 → ZMod 2) + (Pi.single 1 (ε 1) : Fin 4 → ZMod 2) +
      (Pi.single 2 (ε 2) : Fin 4 → ZMod 2) + (Pi.single 3 (ε 3) : Fin 4 → ZMod 2) := by
    funext i
    fin_cases i <;> simp
  have piece : ∀ (i : Fin 4) (g : MulAut (PairN 4)),
      a2Hom (Multiplicative.ofAdd (Pi.single i 1)) = g →
      ∀ c : ZMod 2, (c = 1 → g ∈ H) → a2Hom (Multiplicative.ofAdd (Pi.single i c)) ∈ H := by
    intro i g hg c hc
    rcases zmod_two_cases c with rfl | rfl
    · rw [Pi.single_zero, ofAdd_zero, map_one]
      exact H.one_mem
    · rw [hg]
      exact hc rfl
  rw [hε, ofAdd_add, ofAdd_add, ofAdd_add, map_mul, map_mul, map_mul]
  exact H.mul_mem (H.mul_mem (H.mul_mem (piece 0 _ a2Hom_single_zero _ h0)
    (piece 1 _ a2Hom_single_one _ h1)) (piece 2 _ a2Hom_single_two _ h2))
    (piece 3 _ a2Hom_single_three _ h3)

theorem a2Hom_range : a2Hom.range = A2g := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨ε, rfl⟩ := Multiplicative.ofAdd.surjective x
    exact a2Hom_mem_of_gens ε (fun _ => Subgroup.subset_closure (by simp))
      (fun _ => Subgroup.subset_closure (by simp)) (fun _ => Subgroup.subset_closure (by simp))
      (fun _ => Subgroup.subset_closure (by simp))
  · rw [A2g, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨_, a2Hom_single_zero⟩
    · exact ⟨_, a2Hom_single_one⟩
    · exact ⟨_, a2Hom_single_two⟩
    · exact ⟨_, a2Hom_single_three⟩

theorem a2Hom_mem_A2g (x : Multiplicative (Fin 4 → ZMod 2)) : a2Hom x ∈ A2g :=
  a2Hom_range ▸ ⟨x, rfl⟩

theorem a2Hom_mem_Lg_iff (ε : Fin 4 → ZMod 2) :
    a2Hom (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0 := by
  constructor
  · intro h
    by_contra h3
    obtain ⟨A, hA⟩ := mem_Lg_iff.mp h
    have h1 := congrArg (fun g : MulAut (PairN 4) => g (pairVec (Pi.single 0 1) 0)) hA
    simp only [pairActN_pairVec, a2Hom_apply, Matrix.mulVec_zero] at h1
    have h2 := (pairVec_inj.mp h1).2
    have h4 : A2snd ε (Pi.single 0 1) 0 = A2vec ε (Pi.single 0 1) := by simp [A2snd, h3]
    rw [h4] at h2
    have h5 := A2vec_self ε (Pi.single 0 1)
    rw [← h2, A2vec_zero_vec] at h5
    have h6 := congrFun h5 0
    simp at h6
  · intro h3
    refine a2Hom_mem_of_gens ε (fun _ => pairActN_mem_Lg _) (fun _ => pairActN_mem_Lg _)
      (fun _ => pairActN_mem_Lg _) (fun h => ?_)
    rw [h3] at h
    exact absurd h (by decide)

end CFSG.ASVolI.ChH
