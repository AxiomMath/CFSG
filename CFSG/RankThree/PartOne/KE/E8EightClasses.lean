module

public import CFSG.RankThree.PartOne.KE.E8ClassListsB
public import CFSG.RankThree.PartOne.KE.E8EightLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

@[expose] def e8T8WW : List (Fin Tag.E8.rank) := e8T12Word ++ e8T12Word ++ e8T12Word

@[expose] def e8T8D4Certs : List D4SwapCert := [
  { cls := 0, w := [7, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 2, 0], u := [1, 2, 3], a := 1, b := 4 },
  { cls := 1, w := [6, 5, 4, 3, 1, 2, 0, 3, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 1, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 2, 0], u := [1, 2, 3], a := 1, b := 4 },
  { cls := 2, w := [5, 3, 4, 1, 3, 2, 0, 3, 1, 2, 3, 4, 5, 6, 7, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 3, 4, 5, 6, 1, 3, 4, 5], u := [3, 1, 2], a := 2, b := 4 },
  { cls := 10, w := [7, 3, 1, 4, 3, 2, 0, 3, 4, 5, 6, 1, 3, 4, 5], u := [3, 1, 2], a := 2, b := 4 },
  { cls := 12, w := [6, 7, 1, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 2, 0], u := [3, 2, 4], a := 1, b := 4 },
  { cls := 14, w := [5, 6, 2, 3, 4, 5, 3, 2, 0], u := [2, 4, 3], a := 1, b := 4 }]

@[expose] def e8T8FourA1Certs : List FourA1Cert := [
  { cls := 3, r := [-2, -3, -4, -5, -4, -3, -2, -1] },
  { cls := 4, r := [-2, -2, -4, -5, -4, -3, -2, -1] },
  { cls := 5, r := [-2, -2, -3, -5, -4, -3, -2, -1] },
  { cls := 6, r := [-2, -2, -3, -4, -3, -2, -2, -1] },
  { cls := 7, r := [-2, -2, -3, -4, -3, -2, -1, -1] },
  { cls := 8, r := [-1, -2, -3, -4, -3, -2, -1, -1] },
  { cls := 9, r := [-1, -2, -3, -4, -3, -2, -1, 0] },
  { cls := 11, r := [-1, -2, -2, -3, -3, -3, -2, -1] },
  { cls := 13, r := [-1, -2, -2, -3, -2, -2, -1, 0] },
  { cls := 15, r := [-1, -1, -1, -2, -1, -1, 0, 0] },
  { cls := 16, r := [-1, -1, -1, -2, -1, 0, 0, 0] },
  { cls := 17, r := [-1, -1, -1, -1, -1, -1, -1, 0] }]

theorem e8T8_d4_good : ∀ c ∈ e8T8D4Certs, c.Good e8T8Rows e8T8WW := by
  decide +kernel

theorem e8T8_fourA1_good : ∀ c ∈ e8T8FourA1Certs, c.Good e8T8Rows e8T8VList := by
  decide +kernel

theorem e8T8_class_cover : ∀ j < 18, (∃ c ∈ e8T8D4Certs, c.cls = j) ∨
    ∃ c ∈ e8T8FourA1Certs, c.cls = j := by
  decide +kernel

theorem e8T8_kernel_structure {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (q : ZMod p) ^ 4 + 1 = 0) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e8T8V Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨
      (∃ c ∈ e8T8D4Certs, rootCharKernel a = classSetL e8T8Rows c.cls ∧
        c.Good e8T8Rows e8T8WW) ∨
      (∃ c ∈ e8T8FourA1Certs, rootCharKernel a = classSetL e8T8Rows c.cls ∧
        c.Good e8T8Rows e8T8VList) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := exists_eigencolumn_of_mem_fixedCharTuples e8T8V Fr hFr hp ha hap ha1
  rw [hzk]
  rcases e8T8_root_kernel p hp3 (q : ZMod p) hΦ z hz0 hzM with h | ⟨j, hj, h⟩
  · exact Or.inl h
  · rcases e8T8_class_cover j hj with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact Or.inr (Or.inl ⟨c, hc, h, e8T8_d4_good c hc⟩)
    · exact Or.inr (Or.inr ⟨c, hc, h, e8T8_fourA1_good c hc⟩)

@[expose] def e8T8Alpha0 : List ℤ := [-2, -3, -4, -6, -5, -4, -3, -2]

theorem e8T8Alpha0_mem : e8T8Alpha0 ∈ Tag.E8.artifactRoots ∧
    e8T8Alpha0 ∈ lineClassRoots e8T8Rows 0 := by
  decide +kernel

theorem e8T8Alpha0_not_fourA1 : ∀ c ∈ e8T8FourA1Certs,
    ∀ l ∈ lineClassRoots e8T8Rows c.cls,
      toVec Tag.E8.rank l ≠ toVec Tag.E8.rank e8T8Alpha0 := by
  decide +kernel

end CFSG.RankThree.PartOne.KE
