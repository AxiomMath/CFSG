module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

def IsOrthGL (B : GL (Fin n) (ZMod 2)) : Prop :=
  (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1

theorem IsOrthGL.transpose_eq_inv {B : GL (Fin n) (ZMod 2)} (hB : IsOrthGL B) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  calc (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
      = (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (B : Matrix (Fin n) (Fin n) (ZMod 2))) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
        rw [Matrix.mul_assoc, hB, Matrix.mul_one]

theorem IsOrthGL.dotProduct_mulVec_mulVec {B : GL (Fin n) (ZMod 2)} (hB : IsOrthGL B)
    (x y : Fin n → ZMod 2) :
    ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) ⬝ᵥ ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) =
      x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    hB.transpose_eq_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]

theorem isOrthGL_of_commute_swap {B : GL (Fin n) (ZMod 2)}
    (h : swapN n * pairActN n B = pairActN n B * swapN n) : IsOrthGL B := by
  rw [swapN_mul_pairActN] at h
  have hd : dualGLn n B = B := pairActN_injective (mul_right_cancel h)
  have h1 : (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) =
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [← dualGLn_val, hd]
  have h2 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_transpose] at h2
  unfold IsOrthGL
  rw [← h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem exists_isOrthGL_of_mem_centralizer_swap {g : MulAut (PairN n)}
    (hg : g ∈ Lg n ⊓ Subgroup.centralizer ({swapN n} : Set (MulAut (PairN n)))) :
    ∃ B : GL (Fin n) (ZMod 2), IsOrthGL B ∧ pairActN n B = g := by
  obtain ⟨hL, hC⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨B, rfl⟩ := mem_Lg_iff.mp hL
  exact ⟨B, isOrthGL_of_commute_swap
    (Subgroup.mem_centralizer_iff.mp hC (swapN n) (Set.mem_singleton _)), rfl⟩

noncomputable def orthMatOfMem
    (g : ↥(Lg n ⊓ Subgroup.centralizer ({swapN n} : Set (MulAut (PairN n))))) :
    {B : GL (Fin n) (ZMod 2) // IsOrthGL B} :=
  ⟨(exists_isOrthGL_of_mem_centralizer_swap g.2).choose,
    (exists_isOrthGL_of_mem_centralizer_swap g.2).choose_spec.1⟩

theorem pairActN_orthMatOfMem
    (g : ↥(Lg n ⊓ Subgroup.centralizer ({swapN n} : Set (MulAut (PairN n))))) :
    pairActN n (orthMatOfMem g).1 = g :=
  (exists_isOrthGL_of_mem_centralizer_swap g.2).choose_spec.2

theorem orthMatOfMem_injective : Function.Injective (orthMatOfMem (n := n)) := by
  intro g g' h
  apply Subtype.ext
  rw [← pairActN_orthMatOfMem g, ← pairActN_orthMatOfMem g', h]

end CFSG.ASVolI.ChH
