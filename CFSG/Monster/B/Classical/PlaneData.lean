module

public import CFSG.Fischer.F4
public import Mathlib.Combinatorics.Colex
import all CFSG.Fischer.F4
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Classical.Plane

open CFSG.Fischer
open scoped LinearAlgebra.Projectivization

@[expose] def ΩCode : Fin 21 → Fin 3 → Fin 4 :=
  ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3], ![1, 0, 0], ![1, 0, 1],
    ![1, 0, 2], ![1, 0, 3], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 0],
    ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3]]

@[expose] def Ω (i : Fin 21) : Fin 3 → F4 := fun k => ⟨ΩCode i k⟩

@[expose] def IsNormalized (v : Fin 3 → F4) : Prop :=
  ∃ k : Fin 3, v k = 1 ∧ ∀ j : Fin 3, j < k → v j = 0

instance (v : Fin 3 → F4) : Decidable (IsNormalized v) := by
  unfold IsNormalized; infer_instance

@[expose] def lexKey (v : Fin 3 → F4) : ℕ :=
  16 * (v 0).code.val + 4 * (v 1).code.val + (v 2).code.val

theorem lexKey_lt_iff : ∀ u v : Fin 3 → F4, lexKey u < lexKey v ↔
    ∃ k : Fin 3, (∀ j : Fin 3, j < k → (u j).code = (v j).code) ∧ (u k).code < (v k).code := by
  decide +kernel

theorem Ω_spec : (∀ i, IsNormalized (Ω i)) ∧ (∀ v, IsNormalized v → ∃ i, Ω i = v) ∧
    StrictMono fun i => lexKey (Ω i) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i j h
  revert i j
  decide +kernel

theorem Ω_injective : Function.Injective Ω := by
  intro i j h
  revert i j
  decide +kernel

theorem Ω_ne_zero (i : Fin 21) : Ω i ≠ 0 := by
  revert i
  decide +kernel

@[expose] def normIdx (v : Fin 3 → F4) : Fin 21 :=
  if v 0 ≠ 0 then
    ⟨5 + 4 * ((v 0)⁻¹ * v 1).code.val + ((v 0)⁻¹ * v 2).code.val, by
      have := ((v 0)⁻¹ * v 1).code.isLt
      have := ((v 0)⁻¹ * v 2).code.isLt
      omega⟩
  else if v 1 ≠ 0 then
    ⟨1 + ((v 1)⁻¹ * v 2).code.val, by have := ((v 1)⁻¹ * v 2).code.isLt; omega⟩
  else 0

theorem normIdx_Ω (i : Fin 21) : normIdx (Ω i) = i := by
  revert i
  decide +kernel

theorem normIdx_smul : ∀ (c : F4) (v : Fin 3 → F4), c ≠ 0 → normIdx (c • v) = normIdx v := by
  decide +kernel

theorem exists_smul_Ω_normIdx :
    ∀ v : Fin 3 → F4, v ≠ 0 → ∃ c : F4, c ≠ 0 ∧ v = c • Ω (normIdx v) := by
  decide +kernel

theorem normIdx_unit_smul (a : F4ˣ) (v : Fin 3 → F4) : normIdx (a • v) = normIdx v :=
  normIdx_smul (a : F4) v a.ne_zero

@[expose] noncomputable def Ωproj : Fin 21 ≃ ℙ F4 (Fin 3 → F4) where
  toFun i := Projectivization.mk F4 (Ω i) (Ω_ne_zero i)
  invFun p := normIdx p.rep
  left_inv i := by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F4 (Ω i) (Ω_ne_zero i)
    change normIdx (Projectivization.mk F4 (Ω i) (Ω_ne_zero i)).rep = i
    rw [← ha, normIdx_unit_smul, normIdx_Ω]
  right_inv p := by
    obtain ⟨c, hc, hv⟩ := exists_smul_Ω_normIdx p.rep p.rep_nonzero
    change Projectivization.mk F4 (Ω (normIdx p.rep)) (Ω_ne_zero _) = p
    conv_rhs => rw [← Projectivization.mk_rep p]
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨(Units.mk0 c hc)⁻¹, inv_smul_eq_iff.2 (by rw [Units.smul_def, Units.val_mk0]; exact hv)⟩

theorem Ωproj_apply (i : Fin 21) :
    Ωproj i = Projectivization.mk F4 (Ω i) (Ω_ne_zero i) := rfl

theorem Ωproj_symm_mk (v : Fin 3 → F4) (hv : v ≠ 0) :
    Ωproj.symm (Projectivization.mk F4 v hv) = normIdx v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F4 v hv
  change normIdx (Projectivization.mk F4 v hv).rep = normIdx v
  rw [← ha, normIdx_unit_smul]

@[expose] def projLine (a : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter fun p => ∑ k, Ω a k * Ω p k = 0

@[expose] def Collinear3 (x y z : Fin 21) : Prop :=
  ∃ a, x ∈ projLine a ∧ y ∈ projLine a ∧ z ∈ projLine a

@[expose] def mask {n : ℕ} (A : Finset (Fin n)) : ℕ := ∑ i ∈ A, 2 ^ (i : ℕ)

@[expose] def ofMask {n : ℕ} (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => m.testBit i

theorem testBit_mask {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    (mask A).testBit i ↔ i ∈ A := by
  have h := Finset.toFinset_bitIndices_sum_two_pow (A.map Fin.valEmbedding)
  rw [Finset.sum_map] at h
  have h2 := congrArg ((i : ℕ) ∈ ·) h
  simp only [List.mem_toFinset, Nat.mem_bitIndices, Finset.mem_map, Fin.valEmbedding_apply,
    Fin.val_inj, exists_eq_right, eq_iff_iff] at h2
  exact h2

theorem ofMask_mask {n : ℕ} (A : Finset (Fin n)) : ofMask (mask A) = A := by
  ext i
  simp [ofMask, testBit_mask]

theorem mask_injective {n : ℕ} : Function.Injective (mask (n := n)) := by
  intro A B h
  rw [← ofMask_mask A, h, ofMask_mask]

end CFSG.Monster.B.Classical.Plane
