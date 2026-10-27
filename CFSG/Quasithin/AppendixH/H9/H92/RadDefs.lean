module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def RadMat (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Subgroup (GL (Fin n) (ZMod 2)) where
  carrier := {B | (∀ x : Fin n → ZMod 2,
      ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x ∈ D) ∧
    ∀ u ∈ D, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u}
  one_mem' := by
    refine ⟨fun x => ?_, fun u _ => ?_⟩
    · simp
    · simp
  mul_mem' := by
    rintro B C ⟨hB1, hB2⟩ ⟨hC1, hC2⟩
    refine ⟨fun x => ?_, fun u hu => ?_⟩
    · have hy : ((C : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x ∈ D := hC1 x
      have hBy := hB2 _ hy
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub] at hBy
      have e : (((B * C : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x =
          ((C : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x +
            ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x := by
        rw [Units.val_mul, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
        have h2 : (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            ((C : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) =
            ((C : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x) +
              (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := by
          rw [← hBy]; abel
        rw [h2]; abel
      rw [e]
      exact D.add_mem hy (hB1 x)
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hC2 u hu, hB2 u hu]
  inv_mem' := by
    rintro B ⟨hB1, hB2⟩
    have hinv : ∀ u ∈ D, ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u := by
      intro u hu
      have h := congrArg (fun v => ((B⁻¹ : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) (hB2 u hu)
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h
      exact h.symm
    refine ⟨fun x => ?_, hinv⟩
    have hy : ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x ∈ D := hB1 x
    have h1 := hinv _ hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub] at h1
    have h3 : ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [h3] at h1
    have e : (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x =
        -(((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [← h1]
      abel
    rw [e]
    exact D.neg_mem hy

@[expose] def v1Space (n : ℕ) (U : Subgroup (PairN n)) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {a | pairVec a 0 ∈ U}
  add_mem' := fun {a b} ha hb => by
    have h := U.mul_mem ha hb
    rw [pairVec_mul, add_zero] at h
    exact h
  zero_mem' := by
    show pairVec 0 0 ∈ U
    rw [← pairVec_one]
    exact U.one_mem
  smul_mem' := fun c a ha => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · show pairVec ((0 : ZMod 2) • a) 0 ∈ U
      rw [zero_smul, ← pairVec_one]
      exact U.one_mem
    · simpa using ha

@[expose] def v1Sub (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) : Subgroup (PairN n) where
  carrier := {x | ∃ a ∈ D, x = pairVec a 0}
  one_mem' := ⟨0, D.zero_mem, pairVec_one⟩
  mul_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a + b, D.add_mem ha hb, ?_⟩
    rw [pairVec_mul, add_zero]
  inv_mem' := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a, ha, pairVec_inv a 0⟩

theorem v1Sub_le_V1n {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2)) : v1Sub n D ≤ V1n n := by
  rintro x ⟨a, -, rfl⟩
  exact pairVec_mem_V1n a

theorem v1Space_v1Sub {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    v1Space n (v1Sub n D) = D := by
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    have h := (pairVec_inj.mp hab).1
    rw [h]
    exact hb
  · intro ha
    exact ⟨a, ha, rfl⟩

@[expose] noncomputable def RadV1 (n : ℕ) (U : Subgroup (PairN n)) : Subgroup (MulAut (PairN n)) :=
  (RadMat n (v1Space n U)).map (pairActN n)

theorem RadV1_le_Lg (n : ℕ) (U : Subgroup (PairN n)) : RadV1 n U ≤ Lg n := by
  rintro g ⟨B, -, rfl⟩
  exact pairActN_mem_Lg B

end CFSG.ASVolI.ChH
