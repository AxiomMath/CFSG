module


public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Low-norm virtual-character decomposition

A virtual character with principal coefficient one and norm three or four
is the principal character plus respectively two or three distinct signed
nonprincipal irreducible characters.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Decompose a virtual character whose norm exceeds its principal
coefficient by two or three. -/
public theorem low_norm_virtual_character_decomposition
    {G : Type u} [Group G] [Finite G]
    (zeta : Section1.ClassFunction G) (r : ℕ)
    (hr : r = 2 ∨ r = 3)
    (hzetaVirtual : Theory.Character.IsVirtualCharacter zeta)
    (hzetaPrincipal :
      Section1.scalarProduct G zeta (Section1.principalCharacter G) = 1)
    (hzetaNorm :
      Section1.scalarProduct G zeta zeta = (r : ℂ) + 1) :
    ∃ (chi : Fin r → Section1.ClassFunction G)
        (epsilon : Fin r → ℂ),
      (∀ i, Section1.IsIrreducibleCharacterOnGroup (chi i)) ∧
      Function.Injective chi ∧
      (∀ i, chi i ≠ Section1.principalCharacter G) ∧
      (∀ i, epsilon i = 1 ∨ epsilon i = -1) ∧
      zeta = Section1.principalCharacter G +
        Section1.weightedFamilySum epsilon chi := by
  classical
  let : Fintype (Fin r) := Fintype.ofFinite (Fin r)
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, xi, hxi, b, hb⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let mu : ι → Section1.ClassFunction G :=
    fun i => Section1.ofConjClassFunction (xi i)
  have hmuIrreducible : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (mu i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup
      (hxi.1 i)
  have hmuVirtual : ∀ i, Theory.Character.IsVirtualCharacter (mu i) := by
    intro i
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hmuIrreducible i)
  have hint : ∀ i : ι, ∃ z : ℤ,
      Section1.scalarProduct G zeta (mu i) = (z : ℂ) := by
    intro i
    exact Section1.scalarProduct_isVirtualCharacter_eq_int
      hzetaVirtual (hmuVirtual i)
  let a : Section1.CoeffVector ι :=
    Section3.irreducibleBasisCoeff zeta hint
  have haSpec : ∀ i : ι,
      Section1.scalarProduct G zeta (mu i) = (a i : ℂ) := by
    intro i
    exact Section3.irreducibleBasisCoeff_spec zeta hint i
  have hzetaClass : Section1.IsClassFunction zeta :=
    Section1.isVirtualCharacter_isClassFunction hzetaVirtual
  have hzetaEval : Section1.evalCoeff mu a = zeta := by
    exact Section3.irreducibleBasis_evalCoeff_coeff
      hxi b hb zeta hzetaClass hint
  rcases Section1.exists_principal_index_of_completeFamily (G := G) hxi with
    ⟨i0, hi0⟩
  have hai0Complex : (a i0 : ℂ) = 1 := by
    rw [← haSpec i0]
    change Section1.scalarProduct G zeta
      (Section1.ofConjClassFunction (xi i0)) = 1
    rw [hi0, hzetaPrincipal]
  have hai0 : a i0 = 1 := by
    exact_mod_cast hai0Complex
  have hdotComplex : (Section1.coeffDot a a : ℂ) = (r : ℂ) + 1 := by
    rw [← Section3.irreducibleBasis_scalarProduct_evalCoeff hxi a a,
      hzetaEval, hzetaNorm]
  have hdot : Section1.coeffDot a a = (r : ℤ) + 1 := by
    exact_mod_cast hdotComplex
  have hdotSupport : Section1.coeffDot a a =
      ∑ i ∈ Section1.coeffSupport a, a i * a i := by
    rw [Section1.coeffDot]
    symm
    apply Finset.sum_subset
    · intro i _hi
      simp
    · intro i _hi hiNot
      have hai : a i = 0 :=
        Section1.coeff_eq_zero_of_not_mem_support a hiNot
      simp [hai]
  have hi0Support : i0 ∈ Section1.coeffSupport a := by
    rw [Section1.mem_coeffSupport]
    omega
  let S : Finset ι := (Section1.coeffSupport a).erase i0
  have hsumS : ∑ i ∈ S, a i * a i = (r : ℤ) := by
    have hsplit := Finset.sum_erase_add (Section1.coeffSupport a)
      (fun i => a i * a i) hi0Support
    rw [← hdotSupport, hdot] at hsplit
    simp only [hai0, one_mul] at hsplit
    change (∑ i ∈ (Section1.coeffSupport a).erase i0,
      a i * a i) = (r : ℤ)
    omega
  have hrle : r ≤ 3 := by omega
  have hsign : ∀ i ∈ S, a i = 1 ∨ a i = -1 := by
    intro i hiS
    have hai_ne : a i ≠ 0 := by
      have hiSupport : i ∈ Section1.coeffSupport a :=
        Finset.mem_of_mem_erase hiS
      simpa using (Section1.mem_coeffSupport a i).1 hiSupport
    have hterm_le : a i * a i ≤ ∑ j ∈ S, a j * a j := by
      refine Finset.single_le_sum (N := ℤ) (s := S)
        (f := fun j => a j * a j) ?_ hiS
      intro j _hj
      nlinarith [sq_nonneg (a j)]
    have hsqle : (a i) ^ 2 ≤ 3 := by
      rw [hsumS] at hterm_le
      have hrleInt : (r : ℤ) ≤ 3 := by exact_mod_cast hrle
      nlinarith
    have hsqeq : (a i) ^ 2 = 1 :=
      Int.sq_eq_one_of_sq_le_three hsqle hai_ne
    simpa using (sq_eq_one_iff.mp hsqeq)
  have hcardInt : (S.card : ℤ) = (r : ℤ) := by
    calc
      (S.card : ℤ) = ∑ _i ∈ S, (1 : ℤ) := by simp
      _ = ∑ i ∈ S, a i * a i := by
        refine Finset.sum_congr rfl ?_
        intro i hiS
        rcases hsign i hiS with hi | hi <;> simp [hi]
      _ = (r : ℤ) := hsumS
  have hcard : S.card = r := by exact_mod_cast hcardInt
  let e : Fin r ≃ {i // i ∈ S} :=
    (finCongr hcard.symm).trans S.equivFin.symm
  let chi : Fin r → Section1.ClassFunction G := fun j => mu (e j)
  let epsilon : Fin r → ℂ := fun j => (a (e j) : ℂ)
  refine ⟨chi, epsilon, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hmuIrreducible (e j)
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply hxi.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hij g
  · intro j hj
    have hmuEq : mu (e j) = mu i0 := hj.trans hi0.symm
    have heq : (e j : ι) = i0 := by
      apply hxi.2.2
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact congrFun hmuEq g
    exact (Finset.ne_of_mem_erase (e j).property) heq
  · intro j
    rcases hsign (e j) (e j).property with h | h
    · left
      change (a (e j) : ℂ) = 1
      exact_mod_cast h
    · right
      change (a (e j) : ℂ) = -1
      exact_mod_cast h
  · ext g
    have hsumSupport :
        (∑ i : ι, (a i : ℂ) * mu i g) =
          ∑ i ∈ Section1.coeffSupport a, (a i : ℂ) * mu i g := by
      symm
      apply Finset.sum_subset
      · intro i _hi
        simp
      · intro i _hi hiNot
        have hai : a i = 0 :=
          Section1.coeff_eq_zero_of_not_mem_support a hiNot
        simp [hai]
    calc
      zeta g = Section1.evalCoeff mu a g := congrFun hzetaEval.symm g
      _ = ∑ i : ι, (a i : ℂ) * mu i g := by
        simp [Section1.evalCoeff]
      _ = ∑ i ∈ Section1.coeffSupport a,
          (a i : ℂ) * mu i g := hsumSupport
      _ = (∑ i ∈ S, (a i : ℂ) * mu i g) +
          (a i0 : ℂ) * mu i0 g := by
        simpa [S] using
          (Finset.sum_erase_add (Section1.coeffSupport a)
            (fun i => (a i : ℂ) * mu i g) hi0Support).symm
      _ = Section1.principalCharacter G g +
          ∑ i ∈ S, (a i : ℂ) * mu i g := by
        rw [hai0]
        simp only [mu]
        rw [hi0]
        simp [add_comm]
      _ = Section1.principalCharacter G g +
          ∑ j : Fin r, epsilon j * chi j g := by
        congr 1
        rw [← S.sum_attach]
        simpa [chi, epsilon] using
          (Equiv.sum_comp e
            (fun i : {i // i ∈ S} => (a i : ℂ) * mu i g)).symm
      _ = (Section1.principalCharacter G +
          Section1.weightedFamilySum epsilon chi) g := by
        rfl

end CFSG.GorensteinWalter
