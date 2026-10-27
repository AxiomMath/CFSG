module

public import CFSG.RankThree.PartOne.KE.E6FourSigned
public import CFSG.RankThree.PartOne.KE.E6FourKernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal dualMatrix weylMatrix weylMatrix_mulVec)
open scoped Matrix

theorem neg_sq_add_one_eq_zero_zmod {p q : ℕ} (hΦ : (q : ZMod p) ^ 2 + 1 = 0) :
    (-(q : ZMod p)) ^ 2 + 1 = 0 := by
  linear_combination hΦ

theorem e6TwFour_kernel_of_fixed {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (q : ZMod p) ^ 2 + 1 = 0) {a : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (e6SM (-1)) Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ v : WeylGroup Tag.E6, rootCharKernel a = sigmaSetE6A3 v ∧
      ∃ π : Equiv.Perm (Fin 4), ∀ i j : Fin 4, i ≠ j →
        e6SM (-1) *ᵥ sigmaRootE6A3 v i j = sigmaRootE6A3 v (π i) (π j) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := e6S_eigencolumn_neg Fr hFr hp ha hap ha1
  have hr : (-(q : ZMod p)) ^ 2 + 1 = 0 := neg_sq_add_one_eq_zero_zmod hΦ
  rw [hzk]
  rcases e6Four_kernel_structure hp3 hr z hz0 hzM with h0 | ⟨a', ha1', ha2'⟩
  · exact Or.inl h0
  · obtain ⟨hS, π, hπ⟩ := e6Four_kernel_data a' ha1' ha2'
    refine Or.inr ⟨a'⁻¹, hS, π, fun i j hij => ?_⟩
    have h := hπ i j hij
    rw [e6SM, Matrix.smul_mulVec, h, neg_one_smul, sigmaRootE6A3_neg]

theorem e6TwFour_stab_of_fixed {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf (q : ZMod p) = 4) (hΦ : (q : ZMod p) ^ 2 + 1 = 0)
    {a : Fin Tag.E6.rank → Lˣ} (ha : a ∈ fixedCharTuples (e6SM (-1)) Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.E6)) :=
  rootCharStabilizer_subset_closure_of_fixed (e6SM (-1)) Fr hFr hp ha hap ha1
    (fun z hz hzM => e6Four_dual_stab_le_closure hp (e6Four_p_cases hp hp3 hord)
      (r := -(q : ZMod p)) (neg_sq_add_one_eq_zero_zmod hΦ) hz
      (transpose_eigen_neg (weylMatrix e6F4U) (q : ZMod p) z hzM))

end CFSG.RankThree.PartOne.KE
