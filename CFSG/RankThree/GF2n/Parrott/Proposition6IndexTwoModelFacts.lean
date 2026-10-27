module

public import Certificates.Data.ParrottPSp43
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.ClassicalInvolution.Q3.Q3T6

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def sl23Exps (a b c d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  match a, b, c, d with
  | 0, 1, 2, 0 => (0, 1, 0, 1)
  | 0, 1, 2, 1 => (0, 1, 1, 1)
  | 0, 1, 2, 2 => (0, 1, 2, 1)
  | 0, 2, 1, 0 => (0, 1, 0, 0)
  | 0, 2, 1, 1 => (0, 1, 2, 0)
  | 0, 2, 1, 2 => (0, 1, 1, 0)
  | 1, 0, 0, 1 => (0, 0, 0, 0)
  | 1, 0, 1, 1 => (1, 0, 1, 0)
  | 1, 0, 2, 1 => (1, 1, 2, 0)
  | 1, 1, 0, 1 => (0, 0, 2, 0)
  | 1, 1, 1, 2 => (1, 0, 0, 0)
  | 1, 1, 2, 0 => (1, 1, 1, 0)
  | 1, 2, 0, 1 => (0, 0, 1, 0)
  | 1, 2, 1, 0 => (1, 0, 2, 0)
  | 1, 2, 2, 2 => (1, 1, 0, 0)
  | 2, 0, 0, 2 => (0, 0, 0, 1)
  | 2, 0, 1, 2 => (1, 1, 2, 1)
  | 2, 0, 2, 2 => (1, 0, 1, 1)
  | 2, 1, 0, 2 => (0, 0, 1, 1)
  | 2, 1, 1, 1 => (1, 1, 0, 1)
  | 2, 1, 2, 0 => (1, 0, 2, 1)
  | 2, 2, 0, 2 => (0, 0, 2, 1)
  | 2, 2, 1, 0 => (1, 1, 1, 1)
  | 2, 2, 2, 1 => (1, 0, 0, 1)
  | _, _, _, _ => (0, 0, 0, 0)

@[expose] def sl23Exp (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : ℕ × ℕ × ℕ × ℕ :=
  sl23Exps (A 0 0).val (A 0 1).val (A 1 0).val (A 1 1).val

@[expose] def sl23L1 (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : P45 :=
  alpha1 ^ (sl23Exp A).1 * beta1 ^ (sl23Exp A).2.1 *
    sigma1 ^ (sl23Exp A).2.2.1 * t ^ (sl23Exp A).2.2.2

theorem sl23L1_one : sl23L1 (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 1 := by
  decide +kernel

private theorem sl23L1_mul_genS_aux :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      sl23L1 (A * autGenS) = sl23L1 A * sl23L1 autGenS := by
  decide +kernel

private theorem sl23L1_mul_genT_aux :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      sl23L1 (A * autGenT) = sl23L1 A * sl23L1 autGenT := by
  decide +kernel

private theorem sl23L1_eq_one_aux :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), sl23L1 A = 1 → A = 1 := by
  decide +kernel

private theorem sl23L1_commute_t_aux :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), sl23L1 A * t = t * sl23L1 A := by
  decide +kernel

private theorem sl23L1_genS_commute_conj_u_genS :
    sl23L1 autGenS * (u * sl23L1 autGenS * u) =
      u * sl23L1 autGenS * u * sl23L1 autGenS := by
  decide +kernel

private theorem sl23L1_genS_commute_conj_u_genT :
    sl23L1 autGenS * (u * sl23L1 autGenT * u) =
      u * sl23L1 autGenT * u * sl23L1 autGenS := by
  decide +kernel

private theorem sl23L1_genT_commute_conj_u_genS :
    sl23L1 autGenT * (u * sl23L1 autGenS * u) =
      u * sl23L1 autGenS * u * sl23L1 autGenT := by
  decide +kernel

private theorem sl23L1_genT_commute_conj_u_genT :
    sl23L1 autGenT * (u * sl23L1 autGenT * u) =
      u * sl23L1 autGenT * u * sl23L1 autGenT := by
  decide +kernel

theorem sl23L1_neg_one : sl23L1 (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = t := by
  decide +kernel

private def sl23L1MulSubmonoid : Submonoid (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {B | ∀ A, sl23L1 (A * B) = sl23L1 A * sl23L1 B}
  one_mem' := by
    intro A
    rw [mul_one, sl23L1_one, mul_one]
  mul_mem' := by
    intro B C hB hC A
    calc
      sl23L1 (A * (B * C)) = sl23L1 ((A * B) * C) := by rw [mul_assoc]
      _ = sl23L1 (A * B) * sl23L1 C := hC (A * B)
      _ = (sl23L1 A * sl23L1 B) * sl23L1 C := by rw [hB A]
      _ = sl23L1 A * (sl23L1 B * sl23L1 C) := by rw [mul_assoc]
      _ = sl23L1 A * sl23L1 (B * C) := by rw [hC B]

private theorem sl23L1MulSubmonoid_eq_top : sl23L1MulSubmonoid = ⊤ := by
  rw [eq_top_iff]
  have htop : Submonoid.closure
      ({autGenS, autGenT} : Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, autGen_closure_eq_top,
      Subgroup.top_toSubmonoid]
  rw [← htop, Submonoid.closure_le]
  intro B hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
  rcases hB with rfl | rfl
  · exact sl23L1_mul_genS_aux
  · exact sl23L1_mul_genT_aux

theorem sl23L1_mul (A B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    sl23L1 (A * B) = sl23L1 A * sl23L1 B := by
  have h : B ∈ sl23L1MulSubmonoid := by
    rw [sl23L1MulSubmonoid_eq_top]
    exact Submonoid.mem_top B
  exact h A

@[expose] def sl23L1Hom : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) →* P45 where
  toFun := sl23L1
  map_one' := sl23L1_one
  map_mul' := sl23L1_mul

theorem sl23L1_eq_one {A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)}
    (h : sl23L1 A = 1) : A = 1 :=
  sl23L1_eq_one_aux A h

theorem sl23L1_commute_t (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    sl23L1 A * t = t * sl23L1 A :=
  sl23L1_commute_t_aux A

theorem sl23L1_commute_conj_u (A B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hu : u * u = 1) :
    sl23L1 A * (u * sl23L1 B * u) = u * sl23L1 B * u * sl23L1 A := by
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let s : P45 := sl23L1 autGenS
  let r : P45 := sl23L1 autGenT
  have hH : sl23L1Hom.range = Subgroup.closure ({s, r} : Set P45) := by
    rw [MonoidHom.range_eq_map, ← autGen_closure_eq_top, MonoidHom.map_closure]
    congr 1
    ext x
    simp [s, r, sl23L1Hom]
  let K : Subgroup P45 := sl23L1Hom.range.map (MulAut.conj u).toMonoidHom
  have hK : K = Subgroup.closure ({u * s * u, u * r * u} : Set P45) := by
    rw [show K = sl23L1Hom.range.map (MulAut.conj u).toMonoidHom from rfl, hH,
      MonoidHom.map_closure]
    congr 1
    ext x
    simp [s, r, MulAut.conj_apply, hu_inv]
  have hHK : sl23L1Hom.range ≤ Subgroup.centralizer (K : Set P45) := by
    rw [hH, hK, Subgroup.centralizer_closure, Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer ({u * s * u, u * r * u} : Set P45)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simpa [s, r] using sl23L1_genS_commute_conj_u_genS.symm
    · simpa [s, r] using sl23L1_genS_commute_conj_u_genT.symm
    · simpa [s, r] using sl23L1_genT_commute_conj_u_genS.symm
    · simpa [s, r] using sl23L1_genT_commute_conj_u_genT.symm
  have hA : sl23L1 A ∈ sl23L1Hom.range := MonoidHom.mem_range.2 ⟨A, rfl⟩
  have hB : sl23L1 B ∈ sl23L1Hom.range := MonoidHom.mem_range.2 ⟨B, rfl⟩
  have hBK : u * sl23L1 B * u ∈ K := by
    have hmem : (MulAut.conj u) (sl23L1 B) ∈ K :=
      Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hB
    simpa [MulAut.conj_apply, hu_inv] using hmem
  exact (Subgroup.mem_centralizer_iff.1 (hHK hA) (u * sl23L1 B * u) hBK).symm

end CFSG.RankThree.GF2n.Parrott
