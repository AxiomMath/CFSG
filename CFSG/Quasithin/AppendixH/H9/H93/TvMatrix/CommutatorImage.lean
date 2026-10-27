module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

private theorem vec_sub_eq_add (a b : Fin n → ZMod 2) : a - b = a + b :=
  funext fun i => CharTwo.sub_eq_add (a i) (b i)

private def v1Sub (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    @Subgroup (PairN n) CommGroup.toGroup where
  carrier := {x | ∃ y ∈ U, x = pairVec y 0}
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', U.add_mem hy hy', (pairVec_mul y 0 y' 0).trans (by rw [add_zero])⟩
  one_mem' := ⟨0, U.zero_mem, pairVec_one⟩
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, pairVec_inv y 0⟩

private def imSubOne (A : GL (Fin n) (ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin ((A : Matrix (Fin n) (Fin n) (ZMod 2)) - 1))

private theorem mem_imSubOne {A : GL (Fin n) (ZMod 2)} {x : Fin n → ZMod 2} :
    x ∈ imSubOne A ↔ ∃ y, (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y - y = x := by
  unfold imSubOne
  rw [LinearMap.mem_range]
  simp [Matrix.sub_mulVec]

private def trivOnQuot (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Subgroup (GL (Fin n) (ZMod 2)) where
  carrier := {h | ∀ x, (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x ∈ U}
  mul_mem' := by
    intro h h' hh hh' x
    have e : ((h * h' : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x =
        ((h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((h' : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) -
          (h' : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) +
        ((h' : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x) := by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      abel
    rw [e]
    exact U.add_mem (hh _) (hh' x)
  one_mem' := by
    intro x
    simp
  inv_mem' := by
    intro h hh x
    have h1 := hh ((h⁻¹ : GL (Fin n) (ZMod 2)) *ᵥ x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    have h2 : (h⁻¹ : GL (Fin n) (ZMod 2)).val *ᵥ x - x =
        x - (h⁻¹ : GL (Fin n) (ZMod 2)).val *ᵥ x := by
      rw [vec_sub_eq_add, vec_sub_eq_add, add_comm]
    rw [h2]
    exact h1

private theorem zpow_mulVec_sub_mem (A : GL (Fin n) (ZMod 2)) (k : ℤ) (x : Fin n → ZMod 2) :
    ((A ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x ∈ imSubOne A := by
  have hA : A ∈ trivOnQuot (imSubOne A) := fun x => mem_imSubOne.mpr ⟨x, rfl⟩
  exact (Subgroup.zpow_mem _ hA k) x

private theorem pairActN_pairVec_V1_comm (A : GL (Fin n) (ZMod 2)) (y : Fin n → ZMod 2) :
    pairActN n A (pairVec y 0) * (pairVec y 0)⁻¹ =
      pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y - y) 0 := by
  rw [pairActN_pairVec, Matrix.mulVec_zero, pairVec_inv, pairVec_mul, add_zero, vec_sub_eq_add]

theorem mem_commOn_V1n_zpowers_pairActN (A : GL (Fin n) (ZMod 2)) (x : PairN n) :
    x ∈ commOn (V1n n) (Subgroup.zpowers (pairActN n A)) ↔
      ∃ y : Fin n → ZMod 2, x = pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y - y) 0 := by
  constructor
  · intro hx
    have hle : commOn (V1n n) (Subgroup.zpowers (pairActN n A)) ≤ v1Sub (imSubOne A) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨a, ha, w, hw, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨x, b, rfl⟩ := pairVec_surj w
      have hb : b = 0 := by
        have h2 : (pairVec x b).2 = 1 := mem_V1n.mp hw
        change Multiplicative.ofAdd b = 1 at h2
        simpa using h2
      subst hb
      have e : (pairActN n A ^ k) (pairVec x 0) * (pairVec x 0)⁻¹ =
          pairVec (((A ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x) 0 :=
        (congrArg (fun e : MulAut (PairN n) => e (pairVec x 0) * (pairVec x 0)⁻¹)
          (map_zpow (pairActN n) A k).symm).trans (pairActN_pairVec_V1_comm (A ^ k) x)
      exact ⟨_, zpow_mulVec_sub_mem A k x, e⟩
    obtain ⟨y, hy, rfl⟩ := hle hx
    obtain ⟨z, rfl⟩ := mem_imSubOne.mp hy
    exact ⟨z, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Subgroup.subset_closure ⟨pairActN n A, Subgroup.mem_zpowers _, pairVec y 0,
      pairVec_mem_V1n y, (pairActN_pairVec_V1_comm A y).symm⟩

end CFSG.ASVolI.ChH
