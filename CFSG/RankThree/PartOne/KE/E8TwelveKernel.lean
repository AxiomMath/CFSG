module

public import CFSG.RankThree.PartOne.KE.E8TwelveClasses
public import CFSG.RankThree.PartOne.KE.CTBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

theorem e8T12_kernel_structure {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 = 0) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e8T12V Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨
      (∃ c ∈ e8T12D4Certs, rootCharKernel a = classSetL e8T12Rows c.cls ∧
        c.Good e8T12Rows e8T12WW) ∨
      (∃ c ∈ e8T12TwoA2Certs, rootCharKernel a = classSetL e8T12Rows c.cls ∧
        c.Good e8T12Rows e8T12VList) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := exists_eigencolumn_of_mem_fixedCharTuples e8T12V Fr hFr hp ha hap ha1
  rw [hzk]
  rcases e8T12_root_kernel p hp3 (q : ZMod p) hΦ z hz0 hzM with h | ⟨j, hj, h⟩
  · exact Or.inl h
  · rcases e8T12_class_cover j hj with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact Or.inr (Or.inl ⟨c, hc, h, e8T12_d4_good c hc⟩)
    · exact Or.inr (Or.inr ⟨c, hc, h, e8T12_twoA2_good c hc⟩)

@[expose] def e8T12Alpha0 : List ℤ := [-2, -3, -4, -6, -5, -4, -3, -2]

theorem e8T12Alpha0_mem : e8T12Alpha0 ∈ Tag.E8.artifactRoots ∧
    e8T12Alpha0 ∈ lineClassRoots e8T12Rows 0 := by
  decide +kernel

theorem e8T12Alpha0_not_twoA2 : ∀ c ∈ e8T12TwoA2Certs,
    ∀ l ∈ lineClassRoots e8T12Rows c.cls,
      toVec Tag.E8.rank l ≠ toVec Tag.E8.rank e8T12Alpha0 := by
  decide +kernel

end CFSG.RankThree.PartOne.KE
