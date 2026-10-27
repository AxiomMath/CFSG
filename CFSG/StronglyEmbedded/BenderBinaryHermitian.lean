module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.BenderSuzuki

open CFSG.BenderSuzuki.MatrixGroups
open scoped Matrix

noncomputable section

theorem quadraticBinaryFrobenius_involutive
    (f : ℕ) :
    Function.Involutive
      (FiniteField.Extension.frob (GaloisField 2 f) 2 2).toRingEquiv := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let c := FiniteField.Extension.frob k 2 2
  let : Fintype K := Fintype.ofFinite K
  intro x
  change c (c x) = x
  rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply,
    ← pow_mul, ← pow_two]
  have hcard : Fintype.card K = Nat.card k ^ 2 := by
    rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension]
  rw [← hcard]
  exact FiniteField.pow_card x

theorem quadraticBinaryFrobenius_fixed_card
    (f : ℕ) (hf : 0 < f) :
    Nat.card {x : FiniteField.Extension (GaloisField 2 f) 2 2 //
      (FiniteField.Extension.frob (GaloisField 2 f) 2 2) x = x} = 2 ^ f := by
  classical
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let c := FiniteField.Extension.frob k 2 2
  let Fix := {x : K // c x = x}
  change Nat.card Fix = 2 ^ f
  have hkcard : Nat.card k = 2 ^ f := GaloisField.card 2 f (by omega)
  let embedding : k → Fix := fun x =>
    ⟨algebraMap k K x, c.commutes x⟩
  have hinj : Function.Injective embedding := by
    intro x y hxy
    exact (algebraMap k K).injective (congrArg Subtype.val hxy)
  have hlower : Nat.card k ≤ Nat.card Fix := Nat.card_le_card_of_injective embedding hinj
  let : Fintype K := Fintype.ofFinite K
  let : Fintype Fix := Fintype.ofFinite Fix
  let p : Polynomial K := Polynomial.X ^ Nat.card k - Polynomial.X
  let Z : Finset K := Finset.univ.image (fun x : Fix => (x : K))
  have hZcard : Z.card = Nat.card Fix := by
    rw [Finset.card_image_of_injective _ Subtype.coe_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  have hpne : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K
    (Finite.one_lt_card (α := k))
  have hroot : Z.val ⊆ p.roots := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
    rw [Polynomial.mem_roots hpne]
    change Polynomial.eval (y : K) p = 0
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← FiniteField.Extension.frob_apply k 2 2, y.property, sub_self]
  have hupper := Polynomial.card_le_degree_of_subset_roots hroot
  have hdegree : p.natDegree ≤ Nat.card k := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simpa using (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne' : Nat.card k ≠ 0))
  have hfixcard : Nat.card Fix = Nat.card k :=
    le_antisymm (hZcard ▸ hupper.trans hdegree) hlower
  exact hfixcard.trans hkcard

@[expose] def binaryQuadraticHermitian
    (f : ℕ) (hf : 0 < f) :
    HermitianForm 3 (FiniteField.Extension (GaloisField 2 f) 2 2) where
  conj := (FiniteField.Extension.frob (GaloisField 2 f) 2 2).toRingEquiv
  conj_involutive := quadraticBinaryFrobenius_involutive f
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [GaloisField.card 2 f (by omega : f ≠ 0)]
  form_nondegenerate := by simp [Matrix.det_fin_three]

end

end CFSG.BenderSuzuki
