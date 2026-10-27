module

public import CFSG.Milestones.CL_LIT_AS_vol_I_background

public section

universe u v w

namespace CFSG.Open.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem quasithin_dickson_psl2_subgroups
    (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (H : Subgroup PSL(2, GaloisField p f)) :
    (IsElemAbelian p H ∧ ∃ m : ℕ, m ≤ f ∧ Nat.card H = p ^ m) ∨
    (IsCyclic H ∧ (Nat.card H ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      Nat.card H ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1))) ∨
    (∃ z : ℕ, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    (16 ∣ p ^ (2 * f) - 1 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (P : Subgroup H) (_ : P.Normal), IsElemAbelian p P ∧
      Nat.card P = p ^ m ∧ IsCyclic (H ⧸ P) ∧ Nat.card (H ⧸ P) = t ∧ t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∨
    (∃ m : ℕ, m ∣ f ∧ Nonempty (H ≃* PSL(2, GaloisField p m))) ∨
    (∃ m : ℕ, 2 * m ∣ f ∧ Nonempty (H ≃* PGL(2, GaloisField p m))) :=
  _root_.CFSG.Milestones.cl_lit_as_vol_i_background_1 p f hf H

end CFSG.Open.Open
