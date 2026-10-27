module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderEightQuot
public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Matrix Polynomial

@[expose] def e6P8U : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := -e6Q8W

@[expose] def e6P8UList : List (List ℤ) :=
  [[0, -1, 0, 0, 1, -1], [0, 0, -1, 0, 1, -1], [-1, -1, 0, 0, 1, -1], [0, -1, -1, 0, 1, -1],
   [0, 0, 0, -1, 1, -1], [0, 0, 0, 0, 0, -1]]

@[expose] def e6P8VWord : List (Fin 6) :=
  [0, 1, 2, 3, 4, 3, 2, 4, 3, 4, 2, 0, 5, 2, 4, 3, 4, 2, 5, 0, 1, 3, 2, 4, 3, 1, 0, 5, 2, 4, 3,
    4, 2, 5, 0, 1, 3, 4, 2, 3, 1]

@[expose] def e6P8Rows : List KernelRow := [
  { rep := [-1, -2, -2, -3, -2, -1], fc := [],
    f := [0, 0, 0, 1], h := [0, -1], d := 1,
    q := [-1],
    orbit := [[-1, -2, -2, -3, -2, -1], [1, 1, 2, 3, 2, 1], [0, -1, -1, -2, -2, -1],
      [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 1], [-1, -1, -1, -1, -1, -1],
      [1, 1, 2, 2, 1, 1]] },
  { rep := [-1, -1, -2, -3, -2, -1], fc := [],
    f := [0, 0, 0, 0, -1], h := [1], d := 1,
    q := [-1],
    orbit := [[-1, -1, -2, -3, -2, -1], [0, 1, 1, 2, 2, 1], [0, 0, 0, -1, -1, -1],
      [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, -1], [1, 1, 1, 1, 1, 1], [-1, -1, -2, -2, -1, -1],
      [1, 2, 2, 3, 2, 1]] },
  { rep := [-1, -1, -2, -2, -2, -1], fc := [],
    f := [1, 1, -1, -1, 0, 1], h := [1, -1, 1], d := 1,
    q := [0, 0, -1, 1],
    orbit := [[-1, -1, -2, -2, -2, -1], [0, 1, 1, 2, 1, 1], [-1, -1, -1, -2, -2, -1],
      [0, 0, 1, 1, 1, 1], [0, -1, 0, -1, -1, -1], [1, 0, 1, 1, 1, 1], [0, -1, -1, -1, -1, -1],
      [1, 1, 1, 2, 1, 1]] },
  { rep := [-1, -1, -2, -2, -1, 0], fc := [],
    f := [1, 0, -1], h := [1, 0, 1], d := 2,
    q := [-1],
    orbit := [[-1, -1, -2, -2, -1, 0], [0, 1, 1, 2, 1, 0], [0, 0, 0, -1, -1, 0],
      [-1, -1, -1, -1, 0, 0], [1, 1, 2, 2, 1, 0], [0, -1, -1, -2, -1, 0], [0, 0, 0, 1, 1, 0],
      [1, 1, 1, 1, 0, 0]] },
  { rep := [-1, -1, -1, -2, -1, -1], fc := [],
    f := [-1, 0, 1, 1, -1, -1], h := [0, -1, 1, -1], d := 1,
    q := [-1, 1, -1, 0, 1],
    orbit := [[-1, -1, -1, -2, -1, -1], [1, 1, 2, 2, 2, 1], [0, -1, -1, -2, -1, -1],
      [1, 1, 1, 2, 2, 1], [0, 0, -1, -1, -1, -1], [0, 1, 0, 1, 1, 1], [-1, 0, -1, -1, -1, -1],
      [0, 1, 1, 1, 1, 1]] },
  { rep := [-1, -1, -1, -2, -1, 0], fc := [],
    f := [0, 0, 1, 1, -1, -1], h := [1, -1], d := 2,
    q := [-2, 0, 1],
    orbit := [[-1, -1, -1, -2, -1, 0], [0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 0, 0],
      [0, -1, -1, -1, 0, 0], [1, 1, 1, 2, 1, 0], [0, 0, -1, -1, -1, 0], [-1, 0, -1, 0, 0, 0],
      [0, 1, 1, 1, 0, 0]] },
  { rep := [-1, -1, -1, -1, -1, 0], fc := [],
    f := [1, 1], h := [1, -1, 1, -1], d := 2,
    q := [-1],
    orbit := [[-1, -1, -1, -1, -1, 0], [0, 0, 1, 1, 0, 0], [0, -1, 0, -1, -1, 0],
      [0, -1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0], [0, -1, -1, -1, -1, 0], [0, 0, 0, 1, 0, 0],
      [0, 0, 0, 0, -1, 0]] },
  { rep := [-1, 0, -1, -1, -1, 0], fc := [],
    f := [1, 1, 0, -1, -1], h := [2, -1, 0, 1], d := 2,
    q := [0, 1, -1, -1],
    orbit := [[-1, 0, -1, -1, -1, 0], [-1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
      [0, -1, 0, -1, 0, 0], [1, 0, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0],
      [0, 1, 0, 1, 0, 0]] },
  { rep := [-1, 0, -1, -1, 0, 0], fc := [],
    f := [0, 0, 0, 0, -1, -1], h := [1, -1, 1, -1], d := 2,
    q := [-2, 0, 0, 0, 1],
    orbit := [[-1, 0, -1, -1, 0, 0], [0, 1, 1, 1, 1, 0], [0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 1, 0],
      [1, 1, 1, 1, 1, 0], [0, 0, -1, -1, 0, 0], [0, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0]] }]

theorem e6P8U_eq : e6P8U = toMat Tag.E6.rank e6P8UList := by
  have h : e6P8UList = lsmul Tag.E6.rank (-1) e6Q8WList := by decide +kernel
  rw [e6P8U, e6Q8W_eq, h, toMat_lsmul_neg_one]

theorem e6P8_weyl : ∃ v : WeylGroup Tag.E6, ∀ x : Fin Tag.E6.rank → ℤ,
    v • x = e6P8U *ᵥ permLattice e6Rho x := by
  refine ⟨(coxeterSystem Tag.E6).wordProd (e6Word e6P8VWord), fun x => ?_⟩
  rw [← weylMatrix_mulVec,
    weylMatrix_wordProd_e6 (M := toMat Tag.E6.rank e6P8UList * rhoMatrix) (by decide +kernel),
    permLattice_eq_mulVec, Matrix.mulVec_mulVec, e6P8U_eq]

theorem e6P8_pow : lpow Tag.E6.rank e6P8UList 8 = lid Tag.E6.rank := by
  decide +kernel

theorem e6P8_cyclic : lorbitDet Tag.E6.rank e6P8UList [0, 0, 0, 0, 0, 1] = -1 := by
  decide +kernel

theorem orderOf_e6P8U : orderOf e6P8U = 8 := by
  rw [e6P8U_eq]
  exact orderOf_toMat_eq (by norm_num) e6P8_pow (by decide +kernel)

theorem e6P8_isUnit_det :
    IsUnit (orbitMat (toMat Tag.E6.rank e6P8UList) (toVec Tag.E6.rank [0, 0, 0, 0, 0, 1])
      Tag.E6.rank).det := by
  rw [det_orbitMat_toVec, e6P8_cyclic]
  exact isUnit_one.neg

theorem charpoly_e6P8U : e6P8U.charpoly = (X ^ 4 + 1) * (X ^ 2 - 1) := by
  rw [e6P8U_eq]
  exact charpoly_eq_of_lists (cs := [-1, 0, 1, 0, -1, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [0, 0, 0, 0, 0, 1] e6P8_isUnit_det

theorem e6P8_pair_ne_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) (a : ZMod p)
    (ha : a ^ 4 + 1 = 0) (z : Fin Tag.E6.rank → ZMod p) (hz0 : z ≠ 0)
    (hz : (e6P8U.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z) (α : Fin Tag.E6.rank → ℤ)
    (hα : IsRoot .E6 α) : pair α z ≠ 0 := by
  rw [e6P8U_eq] at hz
  have hΦ : peval [1, 0, 0, 0, 1] a = 0 := by
    have h : peval [1, 0, 0, 0, 1] a = a ^ 4 + 1 := by
      simp only [peval_cons, peval_nil, Int.cast_one, Int.cast_zero]
      ring
    rw [h, ha]
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  have hβ : pair (toVec Tag.E6.rank [0, 0, 0, 0, 0, 1]) z ≠ 0 := by
    intro h0
    apply hz0
    refine eq_zero_of_pair_cols_eq_zero e6P8_isUnit_det fun j => ?_
    change pair ((toMat Tag.E6.rank e6P8UList ^ (j : ℕ)) *ᵥ
      toVec Tag.E6.rank [0, 0, 0, 0, 0, 1]) z = 0
    rw [pair_pow_mulVec hz, h0, mul_zero]
  have hd : ∀ r ∈ e6P8Rows, r.d = 1 ∨ r.d = 2 := by decide +kernel
  have hd' : ∀ r ∈ e6P8Rows, (r.d : ZMod p) ≠ 0 := by
    intro r hr
    rcases hd r hr with h | h <;> rw [h]
    · exact intCast_zmod_ne_zero (by norm_num) (by omega)
    · exact intCast_zmod_ne_zero (by norm_num) (by omega)
  have hker := rootKernel_eq_of_rows (τ := .E6) (F := []) (β := [0, 0, 0, 0, 0, 1])
    (Φ := [1, 0, 0, 0, 1]) (m := 8) (signed := false) e6P8Rows []
    (by decide +kernel) (by decide +kernel) (by simp) hz ha0 hΦ (by simp) hβ hd' (by simp)
  intro h0
  have hmem : α ∈ {α | IsRoot .E6 α ∧ pair α z = 0} := ⟨hα, h0⟩
  rw [hker] at hmem
  obtain ⟨l, hl, -⟩ := hmem
  simp at hl

theorem twisted_E6_Phi8_signed_cyclic_lattice_and_regular_root_characters :
    (∃ v : WeylGroup Tag.E6, ∀ x : Fin Tag.E6.rank → ℤ,
      v • x = e6P8U *ᵥ permLattice e6Rho x) ∧
    orderOf e6P8U = 8 ∧ e6P8U.charpoly = (X ^ 4 + 1) * (X ^ 2 - 1) ∧
    (∃ β, IsRoot .E6 β ∧
      LinearIndependent ℤ (fun j : Fin Tag.E6.rank => (e6P8U ^ (j : ℕ)) *ᵥ β) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E6.rank => (e6P8U ^ (j : ℕ)) *ᵥ β) = ⊤) ∧
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ a : ZMod p, a ^ 4 + 1 = 0 →
      ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
        (e6P8U.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z →
          ∀ α, IsRoot .E6 α → pair α z ≠ 0 := by
  refine ⟨e6P8_weyl, orderOf_e6P8U, charpoly_e6P8U, ?_,
    fun p _ hp a ha z hz0 hz α hα => e6P8_pair_ne_zero p hp a ha z hz0 hz α hα⟩
  rw [e6P8U_eq]
  exact ⟨toVec Tag.E6.rank [0, 0, 0, 0, 0, 1], isRoot_toVec (by decide +kernel),
    (isBasis_iff_isUnit_det _ _).2 e6P8_isUnit_det⟩

end CFSG.RankThree.Lattice
