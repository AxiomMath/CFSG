module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs
public import CFSG.Quasithin.AppendixH.H9.ModelBasic
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

private theorem mP01_23_mulVec (a : Fin 4 → ZMod 2) : mP01_23 *ᵥ a = vP01_23 a := by
  revert a
  decide

private theorem mP02_13_mulVec (a : Fin 4 → ZMod 2) : mP02_13 *ᵥ a = vP02_13 a := by
  revert a
  decide

private theorem mZJ_mulVec (a : Fin 4 → ZMod 2) : mZJ *ᵥ a = vZJ a := by
  revert a
  decide

private theorem mP01_23_transpose : mP01_23ᵀ = mP01_23 := by decide

private theorem mP02_13_transpose : mP02_13ᵀ = mP02_13 := by decide

private theorem mZJ_transpose : mZJᵀ = mZJ := by decide

private theorem pairActN_invGL4_pairVec (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (h : A * A = 1)
    (hT : Aᵀ = A) (a b : Fin 4 → ZMod 2) :
    pairActN 4 (invGL4 A h) (pairVec a b) = pairVec (A *ᵥ a) (A *ᵥ b) := by
  have hd : ((dualGLn 4 (invGL4 A h) : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = A := by
    rw [dualGLn_val]
    exact hT
  rw [pairActN_pairVec, hd]
  rfl

theorem A1_pairActN_gP01_23_pairVec (a b : Fin 4 → ZMod 2) :
    pairActN 4 gP01_23 (pairVec a b) = pairVec (vP01_23 a) (vP01_23 b) := by
  have h := pairActN_invGL4_pairVec mP01_23 mP01_23_sq mP01_23_transpose a b
  rw [mP01_23_mulVec, mP01_23_mulVec] at h
  exact h

theorem A1_pairActN_gP02_13_pairVec (a b : Fin 4 → ZMod 2) :
    pairActN 4 gP02_13 (pairVec a b) = pairVec (vP02_13 a) (vP02_13 b) := by
  have h := pairActN_invGL4_pairVec mP02_13 mP02_13_sq mP02_13_transpose a b
  rw [mP02_13_mulVec, mP02_13_mulVec] at h
  exact h

theorem A1_pairActN_gZJ_pairVec (a b : Fin 4 → ZMod 2) :
    pairActN 4 gZJ (pairVec a b) = pairVec (vZJ a) (vZJ b) := by
  have h := pairActN_invGL4_pairVec mZJ mZJ_sq mZJ_transpose a b
  rw [mZJ_mulVec, mZJ_mulVec] at h
  exact h

theorem A1vec_add (ε a a' : Fin 4 → ZMod 2) :
    A1vec ε (a + a') = A1vec ε a + A1vec ε a' := by
  revert ε a a'
  decide

theorem A1vec_zero_left (a : Fin 4 → ZMod 2) : A1vec 0 a = a := by
  revert a
  decide

theorem A1vec_add_left (ε ε' a : Fin 4 → ZMod 2) :
    A1vec (ε + ε') a = A1vec ε (A1vec ε' a) := by
  revert ε ε' a
  decide

theorem A1vec_involutive (ε a : Fin 4 → ZMod 2) : A1vec ε (A1vec ε a) = a := by
  have h : ε + ε = 0 := by
    revert ε
    decide
  rw [← A1vec_add_left, h, A1vec_zero_left]

private theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem zmod_two_one_ne_zero : ¬ ((1 : ZMod 2) = 0) := by decide

theorem A1fst_zero (a b : Fin 4 → ZMod 2) : A1fst 0 a b = a := by
  simp [A1fst, A1vec_zero_left]

theorem A1snd_zero (a b : Fin 4 → ZMod 2) : A1snd 0 a b = b := by
  simp [A1snd, A1vec_zero_left]

theorem A1fst_add (ε a a' b b' : Fin 4 → ZMod 2) :
    A1fst ε (a + a') (b + b') = A1fst ε a b + A1fst ε a' b' := by
  unfold A1fst
  split_ifs
  · exact A1vec_add ε a a'
  · exact A1vec_add ε b b'

theorem A1snd_add (ε a a' b b' : Fin 4 → ZMod 2) :
    A1snd ε (a + a') (b + b') = A1snd ε a b + A1snd ε a' b' := by
  unfold A1snd
  split_ifs
  · exact A1vec_add ε b b'
  · exact A1vec_add ε a a'

theorem A1fst_involutive (ε a b : Fin 4 → ZMod 2) :
    A1fst ε (A1fst ε a b) (A1snd ε a b) = a := by
  unfold A1fst A1snd
  split_ifs
  · exact A1vec_involutive ε a
  · exact A1vec_involutive ε a

theorem A1snd_involutive (ε a b : Fin 4 → ZMod 2) :
    A1snd ε (A1fst ε a b) (A1snd ε a b) = b := by
  unfold A1fst A1snd
  split_ifs
  · exact A1vec_involutive ε b
  · exact A1vec_involutive ε b

theorem A1fst_add_left (ε ε' a b : Fin 4 → ZMod 2) :
    A1fst (ε + ε') a b = A1fst ε (A1fst ε' a b) (A1snd ε' a b) := by
  have h3 : (ε + ε') 3 = ε 3 + ε' 3 := rfl
  rcases zmod_two_cases (ε 3) with h | h <;> rcases zmod_two_cases (ε' 3) with h' | h' <;>
    simp [A1fst, A1snd, h3, h, h', zmod_two_one_add_one, zmod_two_one_ne_zero, A1vec_add_left]

theorem A1snd_add_left (ε ε' a b : Fin 4 → ZMod 2) :
    A1snd (ε + ε') a b = A1snd ε (A1fst ε' a b) (A1snd ε' a b) := by
  have h3 : (ε + ε') 3 = ε 3 + ε' 3 := rfl
  rcases zmod_two_cases (ε 3) with h | h <;> rcases zmod_two_cases (ε' 3) with h' | h' <;>
    simp [A1fst, A1snd, h3, h, h', zmod_two_one_add_one, zmod_two_one_ne_zero, A1vec_add_left]

end CFSG.ASVolI.ChH
