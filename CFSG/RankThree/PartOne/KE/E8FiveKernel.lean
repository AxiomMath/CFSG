module

public import CFSG.RankThree.PartOne.KE.E8FiveBlock
public import CFSG.RankThree.PartOne.KE.E8A4Sigma
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFive

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal dualMatrix weylMatrix weylMatrix_mulVec chainRoot
  IsNegativeTransition)
open scoped Matrix

theorem e8F5Chain_eq_e8a4chain : e8F5Chain = e8a4chain := by
  funext i
  fin_cases i <;> rfl

theorem e8F5J_eq_e8a4support : e8F5J = e8a4support := rfl

theorem e8Five_kernel_structure {p : ℕ} [Fact p.Prime] (hp5 : 5 < p) (r : ZMod p)
    (hr : r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0) (z : Fin Tag.E8.rank → ZMod p) (hz : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) e8F5U).mulVec z = r • z) :
    e8RootKernel z = ∅ ∨ ∃ a : WeylGroup Tag.E8,
      (fun x => a • x) '' e8RootKernel z = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), ∀ k l, (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l =
        chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain := by
  obtain ⟨-, -, -, -, -, -, h⟩ := E8_order_five_twelve_cyclotomic_lines_and_full_A4_root_kernels
  obtain ⟨-, huniq, -, -, -, -, hlast⟩ := h p hp5 r hr
  obtain ⟨ab, ⟨hab0, rfl⟩, -⟩ := huniq z hz hzr
  rcases hlast ab hab0 with h0 | ⟨-, a, ha1, ha2, ha3⟩
  · exact Or.inl h0
  · obtain ⟨π, -, hπ⟩ := ha2
    exact Or.inr ⟨a, ha1, ⟨π, hπ⟩, ha3⟩

theorem e8Five_kernel_data {S : Set (Fin Tag.E8.rank → ℤ)} (a : WeylGroup Tag.E8)
    (hS : (fun x => a • x) '' S = parabolicRoots Tag.E8 e8F5J)
    (hπ : ∃ π : Equiv.Perm (Fin 5), ∀ k l, (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l =
      chainRoot e8F5Chain (π k) (π l))
    (hneg : IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain)
    (hc21 : weylMatrix (e8F5C ^ 21) = -weylMatrix e8F5U) :
    S = sigmaSetE8A4 a⁻¹ ∧
      (∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
        weylMatrix e8F5U *ᵥ sigmaRootE8A4 a⁻¹ i j = sigmaRootE8A4 a⁻¹ (π i) (π j)) ∧
      (∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
        (-weylMatrix e8F5U) *ᵥ sigmaRootE8A4 a⁻¹ i j = sigmaRootE8A4 a⁻¹ (π j) (π i)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sigmaSetE8A4, ← e8F5J_eq_e8a4support, ← hS, Set.image_image]
    ext x
    simp
  · obtain ⟨π, hπ⟩ := hπ
    refine ⟨π, fun i j _ => ?_⟩
    rw [weylMatrix_mulVec, sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul,
      ← e8F5Chain_eq_e8a4chain, ← mul_smul,
      show e8F5U * a⁻¹ = a⁻¹ * (a * e8F5U * a⁻¹) by group, mul_smul, hπ i j]
  · obtain ⟨π, hπ⟩ := hneg
    have hπ' : ∀ i j, (a * e8F5C ^ 21 * a⁻¹) • chainRoot e8F5Chain i j =
        chainRoot e8F5Chain (π j) (π i) := hπ
    refine ⟨π, fun i j _ => ?_⟩
    rw [← hc21, weylMatrix_mulVec, sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul,
      ← e8F5Chain_eq_e8a4chain, ← mul_smul,
      show e8F5C ^ 21 * a⁻¹ = a⁻¹ * (a * e8F5C ^ 21 * a⁻¹) by group, mul_smul, hπ' i j]

theorem e8Five_kernel_of_fixed (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] (Fr : L →+* L)
    {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hΦ : (((δ : ℤ) : ZMod p) * (q : ZMod p)) ^ 4 + (((δ : ℤ) : ZMod p) * (q : ZMod p)) ^ 3 +
      (((δ : ℤ) : ZMod p) * (q : ZMod p)) ^ 2 + (((δ : ℤ) : ZMod p) * (q : ZMod p)) + 1 = 0)
    {a : Fin Tag.E8.rank → Lˣ} (ha : a ∈ fixedCharTuples (e8FiveM δ) Fr) (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ v : WeylGroup Tag.E8, rootCharKernel a = sigmaSetE8A4 v ∧
      (δ = 1 → ∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
        weylMatrix e8F5U *ᵥ sigmaRootE8A4 v i j = sigmaRootE8A4 v (π i) (π j)) ∧
      (δ = -1 → ∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
        (-weylMatrix e8F5U) *ᵥ sigmaRootE8A4 v i j = sigmaRootE8A4 v (π j) (π i)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := e8Five_eigencolumn δ hδ Fr hFr hp ha hap ha1
  rw [hzk]
  have hr : ((δ : ZMod p) * (q : ZMod p)) ^ 4 + ((δ : ZMod p) * (q : ZMod p)) ^ 3 +
      ((δ : ZMod p) * (q : ZMod p)) ^ 2 + ((δ : ZMod p) * (q : ZMod p)) + 1 = 0 := hΦ
  rcases e8Five_kernel_structure hp5 _ hr z hz0 hzM with h0 | ⟨a', ha1', ha2', ha3'⟩
  · exact Or.inl h0
  · obtain ⟨hS, hs1, hs2⟩ := e8Five_kernel_data a' ha1' ha2' ha3' weylMatrix_e8F5C_21
    exact Or.inr ⟨a'⁻¹, hS, fun _ => hs1, fun _ => hs2⟩

end CFSG.RankThree.PartOne.KE
