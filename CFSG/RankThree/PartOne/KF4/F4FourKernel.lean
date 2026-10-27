module

public import CFSG.RankThree.PartOne.KF4.F4FourBlock
public import CFSG.RankThree.PartOne.KF4.Kernel4
public import CFSG.RankThree.PartOne.KF4.F4ThreeKernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix


theorem weyl_smul_inv_smul' (w a : WeylGroup Tag.F4) (x : Fin Tag.F4.rank → ℤ) :
    w • (a⁻¹ • x) = a⁻¹ • ((a * w * a⁻¹) • x) := by
  rw [smul_smul, smul_smul, show a⁻¹ * (a * w * a⁻¹) = w * a⁻¹ by group]

theorem f4Four_kernel_of_fixed {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {a : Fin Tag.F4.rank → Lˣ} (ha : a ∈ fixedCharTuples (weylMatrix f4W4) Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ v : WeylGroup Tag.F4,
      rootCharKernel a = {r | ∃ r₀ ∈ parabolicRoots Tag.F4 f4B2Support, r = v • r₀} ∧
      ((f4W4 • (v • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ)) = v • f4B2Beta ∧
          f4W4 • (v • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ)) = -(v • f4B2Gamma)) ∨
        (f4W4 • (v • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ)) = -(v • f4B2Beta) ∧
          f4W4 • (v • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ)) = v • f4B2Gamma)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := f4Four_eigencolumn Fr hFr hp ha hap ha1
  rw [hzk]
  rcases f4Four_kernel_structure hp3 _ z hz0 hzM with h0 | ⟨a', hS, hrot⟩
  · exact Or.inl h0
  · right
    refine ⟨a'⁻¹, eq_image_inv_of_image_eq a' hS, ?_⟩
    rw [weyl_smul_inv_smul', weyl_smul_inv_smul']
    rcases hrot with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [h1, h2, weyl_smul_neg]
      exact ⟨rfl, rfl⟩
    · right
      rw [h1, h2, weyl_smul_neg]
      exact ⟨rfl, rfl⟩

end CFSG.RankThree.PartOne.KF4
