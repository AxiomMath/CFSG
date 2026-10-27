module

public import CFSG.Monster.B.Generic.RankFourSpectral
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.B.Generic

open Polynomial Matrix

@[expose] def spectralQ : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 3968055, 0, 0; 1, 46134, 2097152, 1824768; 0, 3510, 837135, 3127410;
    0, 648, 663552, 3303855]

@[expose] noncomputable def spectralF : ℤ[X] :=
  X ^ 3 - C 219069 * X ^ 2 + C 3788665731 * X + C 690573495105

theorem charpoly_spectralQ_int :
    (spectralQ.map (Nat.cast : ℕ → ℤ)).charpoly = (X - C 3968055) * spectralF := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three]
  simp [Matrix.submatrix, Matrix.charmatrix, spectralQ, spectralF, Fin.succAbove]
  ring

theorem charpoly_spectralQ :
    (spectralQ.map (Nat.cast : ℕ → ℚ)).charpoly =
      (X - C ((3968055 : ℕ) : ℚ)) * spectralF.map (Int.castRingHom ℚ) := by
  have h : spectralQ.map (Nat.cast : ℕ → ℚ) =
      (spectralQ.map (Nat.cast : ℕ → ℤ)).map (Int.castRingHom ℚ) := by
    ext i j
    simp
  rw [h, Matrix.charpoly_map, charpoly_spectralQ_int, Polynomial.map_mul, Polynomial.map_sub,
    map_X, map_C]
  simp

theorem spectralF_monic : spectralF.Monic := by
  unfold spectralF
  monicity!

theorem natDegree_spectralF : spectralF.natDegree = 3 := by
  unfold spectralF
  compute_degree!

theorem eval_spectralF_zmod37 (a : ZMod 37) :
    (spectralF.map (Int.castRingHom (ZMod 37))).eval a = a ^ 3 + 8 * a ^ 2 + 4 * a + 13 := by
  simp only [spectralF, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  have h1 : (Int.castRingHom (ZMod 37)) 219069 = 29 := by decide
  have h2 : (Int.castRingHom (ZMod 37)) 3788665731 = 4 := by decide
  have h3 : (Int.castRingHom (ZMod 37)) 690573495105 = 13 := by decide
  have h4 : ∀ b : ZMod 37, b ^ 3 - 29 * b ^ 2 + 4 * b + 13 = b ^ 3 + 8 * b ^ 2 + 4 * b + 13 := by
    decide
  rw [h1, h2, h3, h4]

theorem zmod37_cubic_ne_zero : ∀ a : ZMod 37, a ^ 3 + 8 * a ^ 2 + 4 * a + 13 ≠ 0 := by
  decide

theorem irreducible_spectralF_zmod37 :
    Irreducible (spectralF.map (Int.castRingHom (ZMod 37))) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hdeg : (spectralF.map (Int.castRingHom (ZMod 37))).natDegree = 3 := by
    rw [spectralF_monic.natDegree_map, natDegree_spectralF]
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg]; norm_num)
    (by rw [hdeg])]
  refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
  have hroot := (Polynomial.mem_roots ((spectralF_monic.map _).ne_zero)).1 ha
  rw [Polynomial.IsRoot, eval_spectralF_zmod37] at hroot
  exact zmod37_cubic_ne_zero a hroot

theorem irreducible_spectralF : Irreducible spectralF := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 37)) spectralF
    spectralF_monic irreducible_spectralF_zmod37

theorem irreducible_spectralF_rat : Irreducible (spectralF.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    spectralF_monic.isPrimitive).1 irreducible_spectralF

theorem natDegree_spectralF_rat : (spectralF.map (Int.castRingHom ℚ)).natDegree = 3 := by
  rw [spectralF_monic.natDegree_map, natDegree_spectralF]

theorem sum_spectralQ_zero : ∑ j, spectralQ 0 j = 3968055 := by
  simp [spectralQ, Fin.sum_univ_four]

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem card_eq_of_spectralQ (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (v : V)
    (cell : V → Fin 4) (hcell : ∀ y, cell y = 0 ↔ y = v)
    (hQ : ∀ y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card =
      spectralQ (cell y) j) :
    Fintype.card V = 13548841272 := by
  have h0 : (Finset.univ.filter fun y => cell y = 0).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨v, by ext y; simp [hcell]⟩
  have h01 := card_cell_mul Γ cell spectralQ hQ 0 1
  have h12 := card_cell_mul Γ cell spectralQ hQ 1 2
  have h13 := card_cell_mul Γ cell spectralQ hQ 1 3
  rw [show spectralQ 0 1 = 3968055 from rfl, show spectralQ 1 0 = 1 from rfl, h0] at h01
  rw [show spectralQ 1 2 = 2097152 from rfl, show spectralQ 2 1 = 3510 from rfl] at h12
  rw [show spectralQ 1 3 = 1824768 from rfl, show spectralQ 3 1 = 648 from rfl] at h13
  rw [card_eq_sum_card_cell cell, Fin.sum_univ_four]
  omega

theorem not_three_dvd_card_sub_one : ¬ 3 ∣ (13548841272 : ℕ) - 1 := by
  norm_num

theorem not_equitable_spectralQ (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (hconn : Γ.Connected)
    (cell : V → V → Fin 4) (hcell : ∀ x y, cell x y = 0 ↔ y = x)
    (hQ : ∀ x y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell x z = j).card =
      spectralQ (cell x y) j) : False := by
  have hreg := isRegularOfDegree_of_equitable Γ cell 0 hcell spectralQ hQ
  rw [sum_spectralQ_zero] at hreg
  have hdvd := natDegree_dvd_card_sub_one_of_equitable_charpoly Γ hconn hreg cell 0 hcell
    spectralQ hQ irreducible_spectralF_rat
    (not_isRoot_of_irreducible_of_natDegree_eq_three irreducible_spectralF_rat
      natDegree_spectralF_rat _) charpoly_spectralQ
  obtain ⟨v⟩ := hconn.nonempty
  rw [natDegree_spectralF_rat, card_eq_of_spectralQ Γ v (cell v) (hcell v) (hQ v)] at hdvd
  exact not_three_dvd_card_sub_one hdvd

theorem not_rank_four_spectralQ {G : Type*} [Group G] [MulAction G V]
    [MulAction.IsPretransitive G V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (hΓ : ∀ (g : G) (y z : V), Γ.Adj (g • y) (g • z) ↔ Γ.Adj y z) (hconn : Γ.Connected)
    (v : V) (O : Fin 4 → Set V) (hO : ∀ y, ∃! i, y ∈ O i) (hO0 : O 0 = {v})
    (hQ : ∀ i j, ∀ y ∈ O i, {z | Γ.Adj y z ∧ z ∈ O j}.ncard = spectralQ i j) : False := by
  obtain ⟨cell, hcell, hcQ⟩ := exists_cell_of_partition Γ v O hO 0 hO0 spectralQ hQ
  obtain ⟨cell', hcell', hQ'⟩ := exists_equitable_of_vertexTransitive Γ v
    (exists_iso_of_mulAction Γ hΓ v) cell 0 hcell spectralQ fun y j => (hcQ y 0).2 j
  exact not_equitable_spectralQ Γ hconn cell' hcell' hQ'

end CFSG.Monster.B.Generic
