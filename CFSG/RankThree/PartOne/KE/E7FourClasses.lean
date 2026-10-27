module

public import CFSG.RankThree.PartOne.KE.E7ClassLists
public import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.CTBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

@[expose] def e7F4Word : List (Fin Tag.E7.rank) :=
  [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5]

theorem e7F4_weylImage (u : Fin Tag.E7.rank → ℤ) :
    (coxeterSystem Tag.E7).wordProd e7F4Word • u = e7F4W *ᵥ u := by
  have hw : e7F4Word = ([0, 1, 2, 3, 4, 5] : List (Fin Tag.E7.rank)) ++ [0, 1, 2, 3, 4, 5] ++
      [0, 1, 2, 3, 4, 5] := rfl
  rw [wordProd_smul_eq_wordMat_mulVec, hw, wordMat_append, wordMat_append, e7F4W, e7T12W,
    pow_succ, pow_two]

@[expose] def e7F4Certs : List D4A1Cert := [
  { cls := 0, w := [0, 2, 3, 4, 5, 6, 3, 1, 4, 3, 2, 0, 1, 3, 4, 5], u := [3, 1, 2], a := 1, b := 2,
    r := [0, -1, -1, -2, -1, -1, -1] },
  { cls := 1, w := [2, 3, 1, 4, 5, 6, 3, 4, 5, 3, 2, 0], u := [2, 3, 2], a := 1, b := 2,
    r := [-1, -1, -1, -2, -2, -1, -1] },
  { cls := 2, w := [3, 1, 4, 3, 2, 0, 4, 5, 6, 1, 3, 4, 5], u := [1, 2, 3], a := 1, b := 2,
    r := [-1, -1, -2, -2, -2, -2, -1] },
  { cls := 3, w := [1, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 2, 0], u := [2, 3, 2], a := 1, b := 2,
    r := [0, -1, -1, -2, -1, -1, -1] },
  { cls := 4, w := [5, 6, 2, 3, 1, 4, 3, 2, 0, 1, 3, 4, 5], u := [3, 1, 2], a := 1, b := 2,
    r := [-1, -1, -1, -2, -2, -1, -1] },
  { cls := 5, w := [6, 3, 4, 5, 1, 3, 2, 0], u := [2, 3, 2], a := 1, b := 2,
    r := [-1, -1, -2, -2, -2, -2, -1] }]

theorem e7F4_certs_good : ∀ c ∈ e7F4Certs, c.Good e7F4S0 e7F4Rows e7F4Word := by
  decide +kernel

theorem e7F4_class_cover : ∀ j < 6, ∃ c ∈ e7F4Certs, c.cls = j := by
  decide +kernel

theorem e7F4_kernel_structure {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (q : ZMod p) ^ 2 + 1 = 0) {a : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e7F4W Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l} ∨
      ∃ c ∈ e7F4Certs, rootCharKernel a =
        {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l} ∪ classSetL7 e7F4Rows c.cls ∧
        c.Good e7F4S0 e7F4Rows e7F4Word := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := exists_eigencolumn_of_mem_fixedCharTuples e7F4W Fr hFr hp ha hap ha1
  rw [hzk]
  rcases e7F4_root_kernel p hp3 (q : ZMod p) hΦ z hz0 hzM with h | ⟨j, hj, h⟩
  · exact Or.inl h
  · obtain ⟨c, hc, rfl⟩ := e7F4_class_cover j hj
    exact Or.inr ⟨c, hc, h, e7F4_certs_good c hc⟩

theorem e7F4_d4_cover : ∀ l ∈ Tag.E7.artifactRoots,
    ∃ c ∈ e7F4Certs, l ∈ e7D4RootList.map (lmulVec Tag.E7.rank (e7wl c.w)) := by
  decide +kernel

@[expose] def e7F4ClassRoots : List (List ℤ) := [
  [-2, -2, -3, -4, -3, -2, -1], [-1, -2, -3, -4, -3, -2, -1], [-1, -2, -2, -4, -3, -2, -1],
  [-1, -2, -2, -3, -3, -2, -1], [-1, -2, -2, -3, -2, -2, -1], [-1, -1, -2, -3, -2, -1, -1]]

theorem e7F4_classRoots_isRoot : ∀ j < 6, e7F4ClassRoots.getD j [] ∈ Tag.E7.artifactRoots := by
  decide +kernel

theorem e7F4_classRoots_notS0' : ∀ j < 6, ∀ l ∈ e7F4S0,
    toVec Tag.E7.rank (e7F4ClassRoots.getD j []) ≠ toVec Tag.E7.rank l := by
  decide +kernel

theorem e7F4_classRoots_unique' : ∀ j < 6, ∀ k < 6, ∀ l ∈ lineClassRoots e7F4Rows k,
    toVec Tag.E7.rank (e7F4ClassRoots.getD j []) = toVec Tag.E7.rank l → j = k := by
  decide +kernel

theorem e7F4_certs_cls_lt : ∀ c ∈ e7F4Certs, c.cls < 6 := by decide +kernel

theorem e7F4_certs_w_unique : ∀ c ∈ e7F4Certs, ∀ c' ∈ e7F4Certs, c.cls = c'.cls → c.w = c'.w := by
  decide +kernel

end CFSG.RankThree.PartOne.KE
