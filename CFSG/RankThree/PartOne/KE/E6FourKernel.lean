module

public import CFSG.RankThree.PartOne.KE.E6FourBlock
public import CFSG.RankThree.PartOne.KE.E6A3Sigma
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.Lattice.SteinbergBTE6GaussianLines

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal dualMatrix weylMatrix weylMatrix_mulVec chainRoot chain134
  support134 IsNegativeTransition)
open scoped Matrix

theorem e6Four_p_cases {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hord : orderOf (q : ZMod p) = 4) :
    p = 5 ∨ 7 < p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => by
    rw [h, orderOf_zero] at hord
    omega
  have h4 : 4 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  omega

theorem e6Four_dual_stab_le_closure {p : ℕ} (hp : p.Prime) (hp5 : p = 5 ∨ 7 < p) {r : ZMod p}
    (hr : r ^ 2 + 1 = 0) {z : Fin Tag.E6.rank → ZMod p} (hz : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) e6F4U).mulVec z = r • z) :
    dualWeylStabilizer z ≤ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := by
  rcases hp5 with rfl | hp7
  · have hr5 : ∀ s : ZMod 5, s ^ 2 + 1 = 0 → s = 2 ∨ s = 3 := by decide
    obtain ⟨-, -, -, -, -, h⟩ := E6_order_four_lattice_and_exact_order_five_A3_root_kernels
    obtain ⟨-, hstab, -⟩ := h r (hr5 r hr) z hz hzr
    intro g hg
    exact (hstab g).1 (mem_dualWeylStabilizer_iff_dualMatrix.1 hg)
  · have : Fact p.Prime := ⟨hp⟩
    exact (dualWeylStabilizer_eq_closure (not_dvd_card_weylGroup_E hp hp7 (Or.inl rfl)) z).le

theorem e6Four_kernel_structure {p : ℕ} (hp3 : 3 < p) [Fact p.Prime] {r : ZMod p}
    (hr : r ^ 2 + 1 = 0) (z : Fin Tag.E6.rank → ZMod p) (hz : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) e6F4U).mulVec z = r • z) :
    rootKernel z = ∅ ∨ ∃ a : WeylGroup Tag.E6,
      (fun x => a • x) '' rootKernel z = parabolicRoots Tag.E6 support134 ∧
      IsNegativeTransition (fun x => (a * e6F4U * a⁻¹) • x) chain134 chain134 := by
  obtain ⟨-, h2, -, h4, h5, -, h7⟩ := E6_order_four_six_Gaussian_root_kernel_lines (p := p) hp3 hr
  obtain ⟨⟨a, b⟩, ⟨hab0, rfl⟩, -⟩ := h2 z hz hzr
  by_cases hne : (rootKernel (e6G4Z r a b)).Nonempty
  · right
    have hl := (h4 a b hab0).1 hne
    have h2ne : (2 : ZMod p) ≠ 0 := e6G4_two_ne_zero hp3
    obtain ⟨k, hk⟩ : ∃ k : Fin 6, e6G4LineForm r a b k = 0 := by
      rcases hl with h | h | h | h | h | h
      · exact ⟨0, by simp [e6G4LineForm, h]⟩
      · exact ⟨1, by simp [e6G4LineForm, h]⟩
      · exact ⟨2, by simp [e6G4LineForm, h]⟩
      · exact ⟨3, by simp [e6G4LineForm, h]⟩
      · exact ⟨4, by simp [e6G4LineForm, h]⟩
      · refine ⟨5, ?_⟩
        have h' : (2 : ZMod p) * ((1 - r) * b - a) = 0 := by
          linear_combination (1 - r) * h - a * hr
        have := (mul_eq_zero.1 h').resolve_left h2ne
        simpa [e6G4LineForm] using this
    obtain ⟨hker, -⟩ := h5 a b hab0 k hk
    obtain ⟨-, a₀, ha₀, -, -, hneg⟩ := h7 k
    have hker' : rootKernel (e6G4Z r a b) = {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α} := hker
    exact ⟨a₀, by rw [show rootKernel (e6G4Z r (a, b).1 (a, b).2) = rootKernel (e6G4Z r a b) from
      rfl, hker']; exact ha₀, hneg⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)

theorem e6Four_kernel_data {S : Set (Fin Tag.E6.rank → ℤ)} (a : WeylGroup Tag.E6)
    (hS : (fun x => a • x) '' S = parabolicRoots Tag.E6 support134)
    (hneg : IsNegativeTransition (fun x => (a * e6F4U * a⁻¹) • x) chain134 chain134) :
    S = sigmaSetE6A3 a⁻¹ ∧ ∃ π : Equiv.Perm (Fin 4), ∀ i j : Fin 4, i ≠ j →
      weylMatrix e6F4U *ᵥ sigmaRootE6A3 a⁻¹ i j = sigmaRootE6A3 a⁻¹ (π j) (π i) := by
  refine ⟨?_, ?_⟩
  · rw [sigmaSetE6A3, ← hS, Set.image_image]
    ext x
    simp
  · obtain ⟨π, hπ⟩ := hneg
    have hπ' : ∀ i j : Fin 4, (a * e6F4U * a⁻¹) • chainRoot chain134 i j =
        chainRoot chain134 (π j) (π i) := hπ
    refine ⟨π, fun i j _ => ?_⟩
    rw [weylMatrix_mulVec, sigmaRootE6A3_eq_smul, sigmaRootE6A3_eq_smul, ← mul_smul,
      show e6F4U * a⁻¹ = a⁻¹ * (a * e6F4U * a⁻¹) by group, mul_smul, hπ' i j]

theorem e6Four_kernel_of_fixed {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (q : ZMod p) ^ 2 + 1 = 0) {a : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e6FourM Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ v : WeylGroup Tag.E6, rootCharKernel a = sigmaSetE6A3 v ∧
      ∃ π : Equiv.Perm (Fin 4), ∀ i j : Fin 4, i ≠ j →
        weylMatrix e6F4U *ᵥ sigmaRootE6A3 v i j = sigmaRootE6A3 v (π j) (π i) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := e6Four_eigencolumn Fr hFr hp ha hap ha1
  rw [hzk]
  rcases e6Four_kernel_structure hp3 hΦ z hz0 hzM with h0 | ⟨a', ha1', ha2'⟩
  · exact Or.inl h0
  · obtain ⟨hS, hs⟩ := e6Four_kernel_data a' ha1' ha2'
    exact Or.inr ⟨a'⁻¹, hS, hs⟩

theorem e6Four_stab_of_fixed {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf (q : ZMod p) = 4) (hΦ : (q : ZMod p) ^ 2 + 1 = 0)
    {a : Fin Tag.E6.rank → Lˣ} (ha : a ∈ fixedCharTuples e6FourM Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.E6)) :=
  rootCharStabilizer_subset_closure_of_fixed e6FourM Fr hFr hp ha hap ha1
    (fun _ hz hzM => e6Four_dual_stab_le_closure hp (e6Four_p_cases hp hp3 hord) hΦ hz hzM)

end CFSG.RankThree.PartOne.KE
