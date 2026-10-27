module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs
public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

private theorem pairActN_invGL4_pairVec (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (h : A * A = 1)
    (hs : Aᵀ = A) (a b : Fin 4 → ZMod 2) :
    pairActN 4 (invGL4 A h) (pairVec a b) = pairVec (A *ᵥ a) (A *ᵥ b) := by
  rw [pairActN_pairVec, dualGLn_val]
  have hd : (((invGL4 A h)⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ = A := hs
  rw [hd]
  rfl

private theorem mP01_mulVec : ∀ a : Fin 4 → ZMod 2, mP01 *ᵥ a = vP01 a := by decide
private theorem mP23_mulVec : ∀ a : Fin 4 → ZMod 2, mP23 *ᵥ a = vP23 a := by decide
private theorem mZJ_mulVec : ∀ a : Fin 4 → ZMod 2, mZJ *ᵥ a = vZJ a := by decide

private theorem mP01_transpose : mP01ᵀ = mP01 := by decide
private theorem mP23_transpose : mP23ᵀ = mP23 := by decide
private theorem mZJ_transpose : mZJᵀ = mZJ := by decide

theorem A2g_pairActN_gP01_pairVec (a b : Fin 4 → ZMod 2) :
    pairActN 4 gP01 (pairVec a b) = pairVec (vP01 a) (vP01 b) := by
  rw [gP01, pairActN_invGL4_pairVec mP01 mP01_sq mP01_transpose, mP01_mulVec, mP01_mulVec]

theorem A2g_pairActN_gP23_pairVec (a b : Fin 4 → ZMod 2) :
    pairActN 4 gP23 (pairVec a b) = pairVec (vP23 a) (vP23 b) := by
  rw [gP23, pairActN_invGL4_pairVec mP23 mP23_sq mP23_transpose, mP23_mulVec, mP23_mulVec]

theorem A2g_pairActN_gZJ_pairVec (a b : Fin 4 → ZMod 2) :
    pairActN 4 gZJ (pairVec a b) = pairVec (vZJ a) (vZJ b) := by
  rw [gZJ, pairActN_invGL4_pairVec mZJ mZJ_sq mZJ_transpose, mZJ_mulVec, mZJ_mulVec]

theorem A2vec_zero_vec (ε : Fin 4 → ZMod 2) : A2vec ε 0 = 0 := by
  revert ε
  decide +kernel

theorem A2vec_zero_eps (a : Fin 4 → ZMod 2) : A2vec 0 a = a := by
  revert a
  decide +kernel

private theorem vP01_add : ∀ a a' : Fin 4 → ZMod 2, vP01 (a + a') = vP01 a + vP01 a' := by
  decide +kernel

private theorem vP23_add : ∀ a a' : Fin 4 → ZMod 2, vP23 (a + a') = vP23 a + vP23 a' := by
  decide +kernel

private theorem vZJ_add : ∀ a a' : Fin 4 → ZMod 2, vZJ (a + a') = vZJ a + vZJ a' := by
  decide +kernel

theorem A2vec_add_vec (ε a a' : Fin 4 → ZMod 2) :
    A2vec ε (a + a') = A2vec ε a + A2vec ε a' := by
  unfold A2vec
  split_ifs <;> simp [vP01_add, vP23_add, vZJ_add]

private theorem A2vec_add_eps_bits :
    ∀ e0 e1 e2 f0 f1 f2 : ZMod 2, ∀ a : Fin 4 → ZMod 2,
      A2vec ![e0 + f0, e1 + f1, e2 + f2, 0] a =
        A2vec ![e0, e1, e2, 0] (A2vec ![f0, f1, f2, 0] a) := by
  decide +kernel

theorem A2vec_add_eps (ε ε' a : Fin 4 → ZMod 2) :
    A2vec (ε + ε') a = A2vec ε (A2vec ε' a) :=
  A2vec_add_eps_bits (ε 0) (ε 1) (ε 2) (ε' 0) (ε' 1) (ε' 2) a

theorem A2eps_add_self (ε : Fin 4 → ZMod 2) : ε + ε = 0 := by
  revert ε
  decide +kernel

theorem A2vec_self (ε a : Fin 4 → ZMod 2) : A2vec ε (A2vec ε a) = a := by
  rw [← A2vec_add_eps, A2eps_add_self, A2vec_zero_eps]

theorem A2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

end CFSG.ASVolI.ChH
