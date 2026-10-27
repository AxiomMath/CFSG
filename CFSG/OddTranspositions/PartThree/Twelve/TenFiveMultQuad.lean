module

public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

scoped instance instFactPrimeFiveTenFiveMultQuad : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[expose] def fiveQuad (k : ℕ) (ε : Bool) :
    QuadraticForm (ZMod 5) (Fin (k + 1) → ZMod 5) :=
  (fiveBilin k ε true).toQuadraticMap

theorem fiveQuad_apply (k : ℕ) (ε : Bool) (v : Fin (k + 1) → ZMod 5) :
    fiveQuad k ε v = fiveForm k ε v v := by
  rw [fiveQuad, LinearMap.BilinMap.toQuadraticMap_apply, fiveBilin_apply]
  simp [fiveSignRep]

theorem polar_fiveQuad (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    QuadraticMap.polar (fiveQuad k ε) x y = 2 * fiveForm k ε x y := by
  unfold QuadraticMap.polar
  simp only [fiveQuad_apply]
  rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right,
    fiveForm_comm k ε y x]
  ring

theorem two_ne_zero_five : (2 : ZMod 5) ≠ 0 := by decide

theorem polarBilin_fiveQuad_nondegenerate (k : ℕ) (ε : Bool) :
    (QuadraticMap.polarBilin (fiveQuad k ε)).Nondegenerate := by
  constructor
  · intro x hx
    apply fiveBilin_nondegenerate k ε true x
    intro y
    have h := hx y
    rw [QuadraticMap.polarBilin_apply_apply, polar_fiveQuad] at h
    rw [fiveBilin_apply]
    simpa [fiveSignRep] using (mul_eq_zero.mp h).resolve_left two_ne_zero_five
  · intro y hy
    apply fiveBilin_nondegenerate k ε true y
    intro x
    have h := hy x
    rw [QuadraticMap.polarBilin_apply_apply, polar_fiveQuad] at h
    have h' : fiveForm k ε y x = 0 := by
      rw [fiveForm_comm k ε y x]
      exact (mul_eq_zero.mp h).resolve_left two_ne_zero_five
    rw [fiveBilin_apply]
    simpa [fiveSignRep] using h'

theorem reflect_fiveQuad_eq_toLinEquiv_fiveReflOf (k : ℕ) (ε : Bool)
    (v : Fin (k + 1) → ZMod 5) :
    CFSG.ClassicalGroups.Orthogonal.reflect (fiveQuad k ε) v =
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (k + 1)) (ZMod 5))
        (fiveReflOf k ε v) := by
  ext x
  by_cases hv : fiveQuad k ε v = 0
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hv,
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, fiveReflOf_mulVec]
    have hv' : fiveForm k ε v v = 0 := by rwa [fiveQuad_apply] at hv
    rw [hv', _root_.inv_zero, mul_zero, zero_smul, sub_zero]
    simp
  · have hcoef : QuadraticMap.polar (fiveQuad k ε) v x / fiveQuad k ε v =
        2 * fiveForm k ε x v * (fiveForm k ε v v)⁻¹ := by
      rw [polar_fiveQuad, fiveQuad_apply, fiveForm_comm k ε v x, div_eq_mul_inv]
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hv,
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, fiveReflOf_mulVec, hcoef]

theorem fiveForm_single_self (k : ℕ) (ε : Bool) (i : Fin (k + 1)) (hi : i ≠ Fin.last k) :
    fiveForm k ε (Pi.single i 1) (Pi.single i 1) = 1 := by
  rw [fiveForm_single k ε (Pi.single i 1) i, if_neg hi, Pi.single_eq_same, one_mul]

theorem fiveForm_single_ne (k : ℕ) (ε : Bool) {i j : Fin (k + 1)} (hij : i ≠ j) :
    fiveForm k ε (Pi.single i 1) (Pi.single j 1) = 0 := by
  rw [fiveForm_single k ε (Pi.single i 1) j]
  simp [Pi.single_apply, hij, Ne.symm hij]

theorem fiveForm_e0 (k : ℕ) (hk : 1 ≤ k) (ε : Bool) :
    fiveForm k ε (Pi.single (0 : Fin (k + 1)) 1) (Pi.single (0 : Fin (k + 1)) 1) = 1 := by
  refine fiveForm_single_self k ε 0 ?_
  intro h
  have := congrArg Fin.val h
  simp [Fin.last] at this
  omega

theorem fiveForm_e0_add_e1 (k : ℕ) (hk : 2 ≤ k) (ε : Bool) :
    fiveForm k ε
      (Pi.single (0 : Fin (k + 1)) 1 + Pi.single (⟨1, by omega⟩ : Fin (k + 1)) 1)
      (Pi.single (0 : Fin (k + 1)) 1 + Pi.single (⟨1, by omega⟩ : Fin (k + 1)) 1) = 2 := by
  have h01 : (0 : Fin (k + 1)) ≠ (⟨1, by omega⟩ : Fin (k + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hl0 : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.last] at this
    omega
  have hl1 : (⟨1, by omega⟩ : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.last] at this
    omega
  rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right]
  rw [fiveForm_single_self k ε (0 : Fin (k + 1)) hl0,
    fiveForm_single_ne k ε h01,
    fiveForm_single_ne k ε h01.symm,
    fiveForm_single_self k ε (⟨1, by omega⟩ : Fin (k + 1)) hl1]
  norm_num

theorem exists_mem_fiveReflections (k : ℕ) (hk : 4 ≤ k) (ε π : Bool) :
    ∃ t : GL (Fin (k + 1)) (ZMod 5), t ∈ fiveReflections k ε π := by
  cases π
  · refine ⟨fiveReflOf k ε
        (Pi.single (0 : Fin (k + 1)) 1 + Pi.single (⟨1, by omega⟩ : Fin (k + 1)) 1),
      fiveReflOf_mem ?_ ?_⟩
    · rw [fiveForm_e0_add_e1 k (by omega) ε]
      decide
    · rw [fiveForm_e0_add_e1 k (by omega) ε]
      decide
  · refine ⟨fiveReflOf k ε (Pi.single (0 : Fin (k + 1)) 1), fiveReflOf_mem ?_ ?_⟩
    · rw [fiveForm_e0 k (by omega) ε]
      decide
    · rw [fiveForm_e0 k (by omega) ε]
      decide

end CFSG.OddTranspositions.PartThree
