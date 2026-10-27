module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Statements from BG Appendix C

This file records the statement-only Lean scaffold for Appendix C,
`The Final Contradiction`, from `Local Analysis for the Odd Order Theorem`.
-/

open scoped Pointwise

noncomputable section

universe u v


/-- A nonzero polynomial over a field extension of `ZMod p` that vanishes on
the embedded prime field has degree at least `p`. -/
public theorem CFSG.zmod_card_le_natDegree_of_eval_algebraMap_eq_zero
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Algebra (ZMod p) F]
    (f : Polynomial F) (hf : f ≠ 0)
    (hroot : ∀ x : ZMod p, f.eval (algebraMap (ZMod p) F x) = 0) :
    p ≤ f.natDegree := by
  classical
  let S : Finset F := Finset.univ.image (algebraMap (ZMod p) F)
  have hcardS : S.card = p := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · simp
    · exact FaithfulSMul.algebraMap_injective (ZMod p) F
  have hsubset : S.val ⊆ f.roots := by
    intro y hy
    simp only [S, Finset.mem_val, Finset.mem_image, Finset.mem_univ, true_and] at hy
    rcases hy with ⟨x, rfl⟩
    exact (Polynomial.mem_roots hf).2 (hroot x)
  have hle : S.card ≤ f.natDegree :=
    Polynomial.card_le_degree_of_subset_roots hsubset
  simpa [hcardS] using hle

/-- A linear polynomial with nonzero coefficient of `X` has degree one. -/
public theorem CFSG.polynomial_natDegree_C_mul_X_add_C
    {F : Type*} [Field F] {c d : F} (hc : c ≠ 0) :
    (Polynomial.C c * Polynomial.X + Polynomial.C d : Polynomial F).natDegree = 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · calc
      (Polynomial.C c * Polynomial.X + Polynomial.C d : Polynomial F).natDegree ≤
          max (Polynomial.C c * Polynomial.X : Polynomial F).natDegree
            (Polynomial.C d : Polynomial F).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by
        rw [Polynomial.natDegree_C_mul_X c hc, Polynomial.natDegree_C]
        omega
  · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    simp [hc]

/-- For a surjective homomorphism of finite groups, the kernel has cardinality
`|G| / |H|`. -/
public theorem CFSG.natCard_ker_eq_card_div_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card f.ker = Nat.card G / Nat.card H := by
  have hcard : Nat.card G = Nat.card (G ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := f.ker)
  have hquot : Nat.card (G ⧸ f.ker) = Nat.card H := by
    calc
      Nat.card (G ⧸ f.ker) = Nat.card f.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
      _ = Nat.card (⊤ : Subgroup H) := by
        rw [MonoidHom.range_eq_top_of_surjective f hf]
      _ = Nat.card H := Subgroup.card_top
  exact Nat.eq_div_of_mul_eq_right (ne_of_gt (Nat.card_pos (α := H))) (by
    rw [← hquot]
    exact hcard.symm)

/-- The complex numbers have enough `n`th roots of unity, for nonzero `n`. -/
public theorem CFSG.appendixC_complex_hasEnoughRootsOfUnity (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity ℂ n := by
  exact HasEnoughRootsOfUnity.of_card_le (R := ℂ) (n := n)
    (Complex.card_rootsOfUnity n).ge

/-- Orthogonality for all complex linear characters of a finite abelian group,
using the ambient `Fintype` instance for the character group. -/
public theorem CFSG.appendixC_finite_abelian_character_sum_apply
    {Q : Type*} [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Fintype (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)] (q : Q) :
    (∑ chi : Q →* ℂˣ, (chi q : ℂ)) =
      if q = 1 then (Nat.card Q : ℂ) else 0 := by
  classical
  by_cases hq : q = 1
  · have hcard : Fintype.card (Q →* ℂˣ) = Nat.card Q := by
      rw [← Nat.card_eq_fintype_card]
      exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
    rw [if_pos hq]
    calc
      (∑ chi : Q →* ℂˣ, (chi q : ℂ)) =
          (Fintype.card (Q →* ℂˣ) : ℂ) := by
            simp [hq]
      _ = (Nat.card Q : ℂ) := by
            exact_mod_cast hcard
  · rcases CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q ℂ hq with
      ⟨eta, heta⟩
    let S : ℂ := ∑ chi : Q →* ℂˣ, (chi q : ℂ)
    have hperm :
        S = ∑ chi : Q →* ℂˣ, ((eta * chi) q : ℂ) := by
      simpa [S] using
        (Equiv.sum_comp (Equiv.mulLeft eta)
          (fun chi : Q →* ℂˣ => (chi q : ℂ))).symm
    have hmul :
        (∑ chi : Q →* ℂˣ, ((eta * chi) q : ℂ)) =
          (eta q : ℂ) * S := by
      simp [S, Finset.mul_sum]
    have hfixed : S = (eta q : ℂ) * S := hperm.trans hmul
    have hzero : ((eta q : ℂ) - 1) * S = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr hfixed.symm
    have hetaC : ((eta q : ℂ) - 1) ≠ 0 := by
      intro h
      apply heta
      ext
      exact sub_eq_zero.mp h
    have hSzero : S = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hetaC
    rw [if_neg hq]
    exact hSzero


end
