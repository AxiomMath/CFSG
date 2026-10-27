module

public import CFSG.RankThree.PartOne.KF4.F4ThreeBlock
public import CFSG.RankThree.PartOne.KF4.LongA2Native
public import CFSG.RankThree.PartOne.KF4.ShortA2Fam

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix


theorem parabolicRoots_long_eq :
    parabolicRoots Tag.F4 f4LongSupport =
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot f4chainLong i j} := by
  ext α
  constructor
  · intro hα
    obtain ⟨k, l, hkl, rfl⟩ := exists_f4chainLong_of_mem hα
    exact ⟨k, l, hkl, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact f4chainLong_mem_parabolicRoots hij

theorem parabolicRoots_short_eq :
    parabolicRoots Tag.F4 f4ShortSupport =
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} := by
  ext α
  constructor
  · intro hα
    obtain ⟨k, l, hkl, rfl⟩ := exists_f4ShortSigma_of_mem hα
    exact ⟨k, l, hkl, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact f4ShortSigma_mem_parabolicRoots hij

theorem eq_image_inv_of_image_eq {S T : Set (Fin Tag.F4.rank → ℤ)} (a : WeylGroup Tag.F4)
    (h : (fun x => a • x) '' S = T) : S = {r | ∃ x ∈ T, r = a⁻¹ • x} := by
  ext r
  constructor
  · intro hr
    exact ⟨a • r, h ▸ ⟨r, hr, rfl⟩, by rw [inv_smul_smul]⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← h] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [inv_smul_smul]
    exact hs

theorem f4W3_smul_inv_smul (a : WeylGroup Tag.F4) (x : Fin Tag.F4.rank → ℤ) :
    f4W3 • (a⁻¹ • x) = a⁻¹ • ((a * f4W3 * a⁻¹) • x) := by
  rw [smul_smul, smul_smul, show a⁻¹ * (a * f4W3 * a⁻¹) = f4W3 * a⁻¹ by group]

theorem f4Three_kernel_of_fixed (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {a : Fin Tag.F4.rank → Lˣ} (ha : a ∈ fixedCharTuples (f4ThreeM δ) Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ v : WeylGroup Tag.F4,
      (rootCharKernel a = {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • chainRoot f4chainLong i j} ∧
        ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
          f4W3 • (v • chainRoot f4chainLong i j) = v • chainRoot f4chainLong (π i) (π j)) ∨
      (rootCharKernel a = {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • f4ShortSigma i j} ∧
        ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
          f4W3 • (v • f4ShortSigma i j) = v • f4ShortSigma (π i) (π j)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := f4Three_eigencolumn δ hδ Fr hFr hp ha hap ha1
  rw [hzk]
  rcases f4Three_kernel_structure hp3 _ z hz0 hzM with h0 | ⟨a', hlong | hshort⟩
  · exact Or.inl h0
  · right
    obtain ⟨hS, π, hπ⟩ := hlong
    refine ⟨a'⁻¹, Or.inl ⟨?_, π, fun i j => ?_⟩⟩
    · rw [eq_image_inv_of_image_eq a' hS, parabolicRoots_long_eq]
      ext r
      constructor
      · rintro ⟨x, ⟨i, j, hij, rfl⟩, rfl⟩
        exact ⟨i, j, hij, rfl⟩
      · rintro ⟨i, j, hij, rfl⟩
        exact ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
    · rw [f4W3_smul_inv_smul, hπ i j]
  · right
    obtain ⟨hS, π, hπ⟩ := hshort
    refine ⟨a'⁻¹, Or.inr ⟨?_, π, fun i j => ?_⟩⟩
    · rw [eq_image_inv_of_image_eq a' hS, parabolicRoots_short_eq]
      ext r
      constructor
      · rintro ⟨x, ⟨i, j, hij, rfl⟩, rfl⟩
        exact ⟨i, j, hij, rfl⟩
      · rintro ⟨i, j, hij, rfl⟩
        exact ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
    · rw [f4W3_smul_inv_smul, hπ i j]

end CFSG.RankThree.PartOne.KF4
