module

public import CFSG.RankThree.PartOne.KE.Rank2Lines
public import CFSG.RankThree.PartOne.KE.E7TwelveLattice

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley Matrix Polynomial CFSG.RankThree.Lattice

@[expose] def e7F4W : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := e7T12W ^ 3

@[expose] def e7F4WList : List (List ℤ) :=
  lmul Tag.E7.rank e7T12WList (lmul Tag.E7.rank e7T12WList e7T12WList)

@[expose] def e7F4Phi : List ℤ := [1, 0, 1]

@[expose] def e7F4B2List : List ℤ := lmulVec Tag.E7.rank e7T12WList e7T12VList

@[expose] def e7F4FList : List (List ℤ) := [e7T12AlphaList, e7T12BetaList, e7T12GammaList]

@[expose] def e7F4ColsList : List (List ℤ) :=
  e7F4FList ++ (lorbit Tag.E7.rank e7F4WList e7T12VList 2 ++
    lorbit Tag.E7.rank e7F4WList e7F4B2List 2)

@[expose] def e7F4S0 : List (List ℤ) := e7T12SigmaList

@[expose] def e7F4Rows : List LineRow := [
  { rep := [-2, -2, -3, -4, -3, -2, -1], fc := [-1, 0, 0], a := [-1, -1], b := [0, -1], cls := 0,
    q1 := [], u1 := [-1], u2 := [1], d := 1, q2 := [],
    orbit := [[-2, -2, -3, -4, -3, -2, -1], [-1, -1, -2, -3, -3, -2, -1],
                      [0, 0, 0, 0, -1, -1, -1], [-1, -1, -1, -1, -1, -1, -1]] },
  { rep := [-1, -1, -2, -3, -2, -1, 0], fc := [-1, 1, 0], a := [0, -2], b := [1, -1], cls := 0,
    q1 := [1], u1 := [0, 1], u2 := [], d := 2, q2 := [-2],
    orbit := [[-1, -1, -2, -3, -2, -1, 0], [1, 1, 1, 1, 0, 0, 0],
                      [1, 1, 2, 3, 2, 1, 0], [-1, -1, -1, -1, 0, 0, 0]] },
  { rep := [-1, -1, -2, -2, -1, -1, 0], fc := [-1, 1, 0], a := [-1, -1], b := [0, -1], cls := 0,
    q1 := [], u1 := [-1], u2 := [1], d := 1, q2 := [],
    orbit := [[-1, -1, -2, -2, -1, -1, 0], [0, 0, -1, -1, -1, -1, 0],
                      [1, 1, 1, 2, 1, 0, 0], [0, 0, 0, 1, 1, 0, 0]] },
  { rep := [-1, -1, -1, -2, -1, 0, 0], fc := [-1, 0, 1], a := [-1, -1], b := [0, -1], cls := 0,
    q1 := [], u1 := [-1], u2 := [1], d := 1, q2 := [],
    orbit := [[-1, -1, -1, -2, -1, 0, 0], [0, 0, 0, -1, -1, 0, 0],
                      [1, 1, 2, 2, 1, 1, 0], [0, 0, 1, 1, 1, 1, 0]] },
  { rep := [0, 0, 0, 0, 1, 1, 1], fc := [-1, 1, 1], a := [-1, -1], b := [0, -1], cls := 0,
    q1 := [], u1 := [-1], u2 := [1], d := 1, q2 := [],
    orbit := [[0, 0, 0, 0, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1], [2, 2, 3, 4, 3, 2, 1],
                      [1, 1, 2, 3, 3, 2, 1]] },
  { rep := [-1, -2, -3, -4, -3, -2, -1], fc := [-1, 0, 0], a := [0, -1], b := [0, -1], cls := 1,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[-1, -2, -3, -4, -3, -2, -1], [0, -1, -1, -2, -2, -2, -1],
                      [0, 0, 0, 0, 0, -1, -1], [-1, -1, -2, -2, -1, -1, -1]] },
  { rep := [-1, -1, -2, -2, -2, -1, 0], fc := [0, 0, 0], a := [0, -1], b := [0, -1], cls := 1,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[-1, -1, -2, -2, -2, -1, 0], [0, 0, 0, 0, -1, -1, 0],
                      [0, 1, 1, 2, 1, 0, 0], [-1, 0, -1, 0, 0, 0, 0]] },
  { rep := [-1, -1, -2, -2, -1, 0, 0], fc := [-1, 0, 1], a := [-1, -1], b := [-1, -1], cls := 1,
    q1 := [], u1 := [-1, 1], u2 := [], d := 2, q2 := [-1],
    orbit := [[-1, -1, -2, -2, -1, 0, 0], [0, -1, -1, -2, -2, -1, 0],
                      [1, 1, 2, 2, 1, 0, 0], [0, 1, 1, 2, 2, 1, 0]] },
  { rep := [0, -1, -1, -2, -1, 0, 0], fc := [-1, 0, 1], a := [0, -1], b := [0, -1], cls := 1,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[0, -1, -1, -2, -1, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 2, 2, 2, 1, 0],
                      [0, 0, 0, 0, 1, 1, 0]] },
  { rep := [0, 0, 0, 0, 0, 1, 1], fc := [0, 0, 1], a := [0, -1], b := [0, -1], cls := 1,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[0, 0, 0, 0, 0, 1, 1], [1, 1, 2, 2, 1, 1, 1], [1, 2, 3, 4, 3, 2, 1],
                      [0, 1, 1, 2, 2, 2, 1]] },
  { rep := [-1, -2, -2, -4, -3, -2, -1], fc := [-1, 0, 0], a := [0, -1], b := [1, -1], cls := 2,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[-1, -2, -2, -4, -3, -2, -1], [0, 0, 0, -1, -1, -1, -1],
                      [0, 0, 0, 0, 0, 0, -1], [-1, -2, -2, -3, -2, -1, -1]] },
  { rep := [-1, -2, -2, -3, -2, -1, 0], fc := [-1, 0, 1], a := [-1, -1], b := [0, -2], cls := 2,
    q1 := [-1], u1 := [-1, 1], u2 := [], d := 2, q2 := [-1],
    orbit := [[-1, -2, -2, -3, -2, -1, 0], [0, 0, 0, -1, -1, -1, 0],
                      [1, 2, 2, 3, 2, 1, 0], [0, 0, 0, 1, 1, 1, 0]] },
  { rep := [-1, -1, -1, -2, -2, -1, 0], fc := [0, 0, 0], a := [0, -1], b := [1, -1], cls := 2,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[-1, -1, -1, -2, -2, -1, 0], [0, 1, 1, 1, 0, 0, 0],
                      [0, 1, 1, 2, 1, 1, 0], [-1, -1, -1, -1, -1, 0, 0]] },
  { rep := [0, -1, -1, -2, -1, -1, 0], fc := [-1, 1, 0], a := [0, -1], b := [1, -1], cls := 2,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[0, -1, -1, -2, -1, -1, 0], [1, 1, 1, 1, 1, 0, 0], [1, 1, 1, 2, 2, 1, 0],
                      [0, -1, -1, -1, 0, 0, 0]] },
  { rep := [0, 0, 0, 0, 0, 0, 1], fc := [0, 1, 0], a := [0, -1], b := [1, -1], cls := 2,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[0, 0, 0, 0, 0, 0, 1], [1, 2, 2, 3, 2, 1, 1], [1, 2, 2, 4, 3, 2, 1],
                      [0, 0, 0, 1, 1, 1, 1]] },
  { rep := [-1, -2, -2, -3, -3, -2, -1], fc := [0, -1, 0], a := [], b := [0, -1], cls := 3,
    q1 := [], u1 := [], u2 := [0, 1], d := 1, q2 := [-1],
    orbit := [[-1, -2, -2, -3, -3, -2, -1], [-1, -1, -1, -2, -2, -2, -1],
                      [-1, 0, -1, -1, -1, -1, -1], [-1, -1, -2, -2, -2, -1, -1]] },
  { rep := [0, -1, -1, -1, -1, -1, 0], fc := [0, 0, 0], a := [], b := [0, -1], cls := 3,
    q1 := [], u1 := [], u2 := [0, 1], d := 1, q2 := [-1],
    orbit := [[0, -1, -1, -1, -1, -1, 0], [0, 0, 0, 0, 0, -1, 0],
                      [0, 1, 0, 1, 1, 0, 0], [0, 0, -1, 0, 0, 0, 0]] },
  { rep := [0, -1, -1, -1, -1, 0, 0], fc := [0, -1, 1], a := [], b := [-1, -1], cls := 3,
    q1 := [], u1 := [], u2 := [-1, 1], d := 2, q2 := [-1],
    orbit := [[0, -1, -1, -1, -1, 0, 0], [0, -1, 0, -1, -1, -1, 0],
                      [0, 1, 1, 1, 1, 0, 0], [0, 1, 0, 1, 1, 1, 0]] },
  { rep := [0, -1, 0, -1, -1, 0, 0], fc := [0, -1, 1], a := [], b := [0, -1], cls := 3,
    q1 := [], u1 := [], u2 := [0, 1], d := 1, q2 := [-1],
    orbit := [[0, -1, 0, -1, -1, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 1, 1, 1, 1, 0],
                      [0, 0, 0, 0, 0, 1, 0]] },
  { rep := [1, 0, 1, 1, 1, 1, 1], fc := [0, 0, 1], a := [], b := [0, -1], cls := 3,
    q1 := [], u1 := [], u2 := [0, 1], d := 1, q2 := [-1],
    orbit := [[1, 0, 1, 1, 1, 1, 1], [1, 1, 2, 2, 2, 1, 1], [1, 2, 2, 3, 3, 2, 1],
                      [1, 1, 1, 2, 2, 2, 1]] },
  { rep := [-1, -2, -2, -3, -2, -2, -1], fc := [-1, 0, 0], a := [-1], b := [0, -1], cls := 4,
    q1 := [], u1 := [-1], u2 := [], d := 1, q2 := [],
    orbit := [[-1, -2, -2, -3, -2, -2, -1], [-1, -1, -2, -3, -2, -2, -1],
                      [0, 0, -1, -1, -1, -1, -1], [0, -1, -1, -1, -1, -1, -1]] },
  { rep := [-1, -1, -1, -2, -1, -1, 0], fc := [-1, 1, 0], a := [-1, -1], b := [1, -1], cls := 4,
    q1 := [1], u1 := [-1, 1], u2 := [], d := 2, q2 := [-1],
    orbit := [[-1, -1, -1, -2, -1, -1, 0], [0, 1, 0, 0, 0, 0, 0],
                      [1, 1, 1, 2, 1, 1, 0], [0, -1, 0, 0, 0, 0, 0]] },
  { rep := [-1, -1, -1, -1, -1, -1, 0], fc := [0, 0, 0], a := [-1], b := [0, -1], cls := 4,
    q1 := [], u1 := [-1], u2 := [], d := 1, q2 := [],
    orbit := [[-1, -1, -1, -1, -1, -1, 0], [-1, 0, -1, -1, -1, -1, 0],
                      [0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0]] },
  { rep := [0, -1, 0, -1, 0, 0, 0], fc := [-1, 0, 1], a := [-1], b := [0, -1], cls := 4,
    q1 := [], u1 := [-1], u2 := [], d := 1, q2 := [],
    orbit := [[0, -1, 0, -1, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0],
                      [1, 0, 1, 1, 1, 1, 0]] },
  { rep := [0, 0, 1, 1, 1, 1, 1], fc := [0, 0, 1], a := [-1], b := [0, -1], cls := 4,
    q1 := [], u1 := [-1], u2 := [], d := 1, q2 := [],
    orbit := [[0, 0, 1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1], [1, 2, 2, 3, 2, 2, 1],
                      [1, 1, 2, 3, 2, 2, 1]] },
  { rep := [-1, -1, -2, -3, -2, -1, -1], fc := [-1, 0, 0], a := [0, -1], b := [], cls := 5,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[-1, -1, -2, -3, -2, -1, -1], [0, -1, -1, -2, -2, -1, -1],
                      [0, -1, 0, -1, -1, -1, -1], [-1, -1, -1, -2, -1, -1, -1]] },
  { rep := [-1, 0, -1, -1, -1, 0, 0], fc := [0, 0, 0], a := [0, -1], b := [], cls := 5,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[-1, 0, -1, -1, -1, 0, 0], [0, 0, 0, 0, -1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
                      [-1, 0, 0, 0, 0, 0, 0]] },
  { rep := [-1, 0, -1, -1, 0, 0, 0], fc := [-1, 1, 0], a := [-1, -1], b := [], cls := 5,
    q1 := [], u1 := [-1, 1], u2 := [], d := 2, q2 := [-1],
    orbit := [[-1, 0, -1, -1, 0, 0, 0], [0, 0, -1, -1, -1, 0, 0],
                      [1, 0, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0]] },
  { rep := [0, 0, -1, -1, 0, 0, 0], fc := [-1, 1, 0], a := [0, -1], b := [], cls := 5,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[0, 0, -1, -1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0],
                      [0, 0, 0, 0, 1, 0, 0]] },
  { rep := [0, 1, 0, 1, 1, 1, 1], fc := [0, 1, 0], a := [0, -1], b := [], cls := 5,
    q1 := [], u1 := [0, 1], u2 := [], d := 1, q2 := [-1],
    orbit := [[0, 1, 0, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1, 1], [1, 1, 2, 3, 2, 1, 1],
                      [0, 1, 1, 2, 2, 1, 1]] }]

@[expose] def e7F4Classes : List LineClass := [
  { A := [-1, -1], B := [0, -1], u1 := [-1], u2 := [1], d := 1, q := [] },
  { A := [0, -1], B := [0, -1], u1 := [0, 1], u2 := [], d := 1, q := [-1] },
  { A := [0, -1], B := [1, -1], u1 := [0, 1], u2 := [], d := 1, q := [-1] },
  { A := [], B := [0, -1], u1 := [], u2 := [0, 1], d := 1, q := [-1] },
  { A := [-1], B := [0, -1], u1 := [-1], u2 := [], d := 1, q := [] },
  { A := [0, -1], B := [], u1 := [0, 1], u2 := [], d := 1, q := [-1] }]

@[expose] def e7F4Crosses : List CrossCert := [
  { i := 0, j := 1, u := [0, -1], d := 1, q := [-1] },
  { i := 0, j := 2, u := [-1], d := 1, q := [] },
  { i := 0, j := 3, u := [-1, -1], d := 2, q := [-2, -1] },
  { i := 0, j := 4, u := [-1], d := 1, q := [-1] },
  { i := 0, j := 5, u := [1], d := 1, q := [-1] },
  { i := 1, j := 2, u := [0, 1], d := 1, q := [-1] },
  { i := 1, j := 3, u := [-1], d := 1, q := [-1] },
  { i := 1, j := 4, u := [-1, 1], d := 2, q := [-2, 1] },
  { i := 1, j := 5, u := [1], d := 1, q := [-1] },
  { i := 2, j := 3, u := [-1], d := 1, q := [-1] },
  { i := 2, j := 4, u := [0, 1], d := 1, q := [-1, 1] },
  { i := 2, j := 5, u := [1, -1], d := 2, q := [-2, 1] },
  { i := 3, j := 4, u := [0, 1], d := 1, q := [-1] },
  { i := 3, j := 5, u := [1], d := 1, q := [-1] },
  { i := 4, j := 5, u := [1], d := 1, q := [-1] }]


theorem e7F4W_eq : e7F4W = toMat Tag.E7.rank e7F4WList := by
  rw [e7F4W, pow_succ', pow_two, e7T12W_eq, e7F4WList, toMat_lmul, toMat_lmul]

theorem e7F4Cols_det : (toMat Tag.E7.rank (lcols Tag.E7.rank e7F4ColsList)).det = -1 := by
  rw [det_toMat_eq]
  decide +kernel

theorem e7F4_rows_check : ∀ r ∈ e7F4Rows,
    r.check Tag.E7.rank e7F4WList e7F4FList e7T12VList e7F4B2List e7F4Phi 4
      (e7F4Classes.getD r.cls default) = true := by
  decide +kernel

theorem e7F4_rows_cls : ∀ r ∈ e7F4Rows, r.cls < e7F4Classes.length := by decide +kernel

theorem e7F4_classes_check : ∀ c ∈ e7F4Classes, c.check e7F4Phi = true := by decide +kernel

theorem e7F4_cross' : ∀ i j : Fin e7F4Classes.length, i ≠ j →
    ∃ c ∈ e7F4Crosses, (c.i = i.val ∧ c.j = j.val) ∨ (c.i = j.val ∧ c.j = i.val) := by
  decide +kernel

theorem e7F4_cross : ∀ i j, i < e7F4Classes.length → j < e7F4Classes.length → i ≠ j →
    ∃ c ∈ e7F4Crosses, (c.i = i ∧ c.j = j) ∨ (c.i = j ∧ c.j = i) := fun i j hi hj hij =>
  e7F4_cross' ⟨i, hi⟩ ⟨j, hj⟩ fun h => hij (congrArg Fin.val h)

theorem e7F4_cross_check : ∀ c ∈ e7F4Crosses, c.check e7F4Phi e7F4Classes = true := by
  decide +kernel

theorem e7F4_cover : ∀ l ∈ Tag.E7.artifactRoots,
    l ∈ e7F4S0 ∨ ∃ r ∈ e7F4Rows, l ∈ r.orbit := by
  decide +kernel

theorem e7F4_S0_roots : ∀ l ∈ e7F4S0, l ∈ Tag.E7.artifactRoots := by
  decide +kernel

theorem e7F4_orbit_roots :
    ∀ r ∈ e7F4Rows, ∀ l ∈ r.orbit, l ∈ Tag.E7.artifactRoots := by
  decide +kernel

theorem e7F4_d_rows : ∀ r ∈ e7F4Rows, r.d = 1 ∨ r.d = 2 := by decide +kernel

theorem e7F4_d_classes : ∀ c ∈ e7F4Classes, c.d = 1 := by decide +kernel

theorem e7F4_d_crosses : ∀ c ∈ e7F4Crosses, c.d = 1 ∨ c.d = 2 := by decide +kernel

theorem e7F4W_fixes : ∀ x ∈ e7F4FList, lmulVec Tag.E7.rank e7F4WList x = x := by decide +kernel

theorem e7F4_cols_pair {p : ℕ} [Fact p.Prime] {ρ : ZMod p} {z : Fin Tag.E7.rank → ZMod p}
    (hz : ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z)
    (hF : ∀ x ∈ e7F4FList, pair (toVec Tag.E7.rank x) z = 0)
    (h1 : pair (toVec Tag.E7.rank e7T12VList) z = 0)
    (h2 : pair (toVec Tag.E7.rank e7F4B2List) z = 0) (j : Fin Tag.E7.rank) :
    pair (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7F4ColsList) i j) z = 0 := by
  have hcol : (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7F4ColsList) i j) =
      toVec Tag.E7.rank (e7F4ColsList.getD j []) := by
    funext i
    rw [toMat_lcols]
    rfl
  rw [hcol]
  have hj : (j : ℕ) < 7 := j.isLt
  by_cases h3 : (j : ℕ) < 3
  · simp only [e7F4ColsList]
    rw [List.getD_append _ _ _ _ (by simp [e7F4FList]; omega)]
    apply hF
    have hlen : (j : ℕ) < e7F4FList.length := by simp [e7F4FList]; omega
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  · by_cases h5 : (j : ℕ) < 5
    · simp only [e7F4ColsList]
      rw [List.getD_append_right _ _ _ _ (by simp [e7F4FList]; omega)]
      have h4 : (j : ℕ) - e7F4FList.length = (j : ℕ) - 3 := by simp [e7F4FList]
      rw [h4, List.getD_append _ _ _ _ (by simp [lorbit]; omega),
        toVec_lorbit_getD (by omega), pair_pow_mulVec hz, h1, mul_zero]
    · simp only [e7F4ColsList]
      rw [List.getD_append_right _ _ _ _ (by simp [e7F4FList]; omega)]
      have h4 : (j : ℕ) - e7F4FList.length = (j : ℕ) - 3 := by simp [e7F4FList]
      rw [h4, List.getD_append_right _ _ _ _ (by simp [lorbit]; omega)]
      have h6 : (j : ℕ) - 3 - (lorbit Tag.E7.rank e7F4WList e7T12VList 2).length = (j : ℕ) - 5 := by
        simp [lorbit]
        omega
      rw [h6, toVec_lorbit_getD (by omega), pair_pow_mulVec hz, h2, mul_zero]

theorem e7F4_root_kernel (p : ℕ) [Fact p.Prime] (hp3 : 3 < p)
    (ρ : ZMod p) (hρ : ρ ^ 2 + 1 = 0) (z : Fin Tag.E7.rank → ZMod p) (hz0 : z ≠ 0)
    (hz : (e7F4W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z) :
    {r | IsRoot .E7 r ∧ pair r z = 0} = {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l} ∨ ∃ j < 6,
      {r | IsRoot .E7 r ∧ pair r z = 0} =
        {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l} ∪
          {α | ∃ l ∈ lineClassRoots e7F4Rows j, α = toVec Tag.E7.rank l} := by
  rw [e7F4W_eq] at hz
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    simp at hρ
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    have h2 : ((2 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination hρ
    exact intCast_zmod_ne_zero (by norm_num) (by omega) h2
  have hΦ : peval e7F4Phi ρ = 0 := by
    have h : peval e7F4Phi ρ = ρ ^ 2 + 1 := by
      simp only [e7F4Phi, peval_cons, peval_nil, Int.cast_one, Int.cast_zero]
      ring
    rw [h, hρ]
  have hF : ∀ x ∈ e7F4FList, pair (toVec Tag.E7.rank x) z = 0 := by
    intro x hx
    have hfix : (toMat Tag.E7.rank e7F4WList) *ᵥ toVec Tag.E7.rank x = toVec Tag.E7.rank x := by
      rw [← toVec_lmulVec, e7F4W_fixes x hx]
    have h := pair_mulVec hz (toVec Tag.E7.rank x)
    rw [hfix] at h
    have h2 : (1 - ρ) * pair (toVec Tag.E7.rank x) z = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hρ1.symm)
  have hS0z : ∀ l ∈ e7F4S0, pair (toVec Tag.E7.rank l) z = 0 := by
    intro l hl
    simp only [e7F4S0, e7T12SigmaList, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hF _ (by simp [e7F4FList])
    · rw [toVec_vneg, pair_neg, hF _ (by simp [e7F4FList])]
      exact neg_zero
    · exact hF _ (by simp [e7F4FList])
    · rw [toVec_vneg, pair_neg, hF _ (by simp [e7F4FList])]
      exact neg_zero
    · exact hF _ (by simp [e7F4FList])
    · rw [toVec_vneg, pair_neg, hF _ (by simp [e7F4FList])]
      exact neg_zero
  have hst : ¬ (pair (toVec Tag.E7.rank e7T12VList) z = 0 ∧
      pair (toVec Tag.E7.rank e7F4B2List) z = 0) := by
    rintro ⟨h1, h2⟩
    apply hz0
    exact eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E7.rank (lcols Tag.E7.rank e7F4ColsList))
      (by rw [e7F4Cols_det]; exact isUnit_one.neg) fun j => e7F4_cols_pair hz hF h1 h2 j
  have hlen : e7F4Classes.length = 6 := by decide +kernel
  have hp0 : ∀ d : ℤ, 0 < d → d < p → (d : ZMod p) ≠ 0 := fun d hd hdp =>
    intCast_zmod_ne_zero hd hdp
  have h := rootKernel_eq_of_lines (τ := .E7) (W := e7F4WList) (F := e7F4FList)
    (β₁ := e7T12VList) (β₂ := e7F4B2List) (Φ := e7F4Phi) (m := 4) e7F4Rows e7F4Classes
    e7F4Crosses e7F4S0 e7F4_rows_check e7F4_rows_cls e7F4_classes_check e7F4_cross
    e7F4_cross_check e7F4_cover e7F4_S0_roots e7F4_orbit_roots hz hρ0 hΦ hF hS0z hst
    (fun r hr => by
      rcases e7F4_d_rows r hr with h | h <;> rw [h] <;>
        exact hp0 _ (by norm_num) (by omega))
    (fun c hc => by rw [e7F4_d_classes c hc]; exact hp0 1 (by norm_num) (by omega))
    (fun c hc => by
      rcases e7F4_d_crosses c hc with h | h <;> rw [h] <;>
        exact hp0 _ (by norm_num) (by omega))
  rw [hlen] at h
  simpa using h

end CFSG.RankThree.PartOne.KE
