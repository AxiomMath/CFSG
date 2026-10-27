
module

public import CFSG.Sporadic.Schreier.J4SFiveBase

public import CFSG.Sporadic.Schreier.J4SPrimesCheck
public import CFSG.Sporadic.Schreier.J4SGLBase1
public import CFSG.Sporadic.Schreier.J4SFrattiniBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SKCent

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem bounded_powCols :
    ∀ (m : ℕ) {C : Array ℕ}, Bounded C → Bounded (powCols C m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hC
    rw [powCols]
    split_ifs
    · exact idRows_bounded
    · exact bounded_comp11 hC (ih _ (by omega) (bounded_comp11 hC hC))
    · exact ih _ (by omega) (bounded_comp11 hC hC)

theorem colsOf_spec
    {k : J} (hk : k ∈ K) : ActsBy k (colsOf k) ∧ Bounded (colsOf k) := by
  classical
  have hex : ∀ j : Fin 11, ∃ a < 2048, η a = k * u j * k⁻¹ := fun j =>
    exists_η_eq (conj_mem_N_of_mem_K hk (u_mem_N j))
  have hget : ∀ j : Fin 11, (colsOf k)[j.val]! = Classical.choose (hex j) := by
    intro j
    unfold colsOf
    rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn, dite_eq_left (hex j)]
  refine ⟨conj_η_of_cols fun j => ?_, by simp [colsOf], fun j hj => ?_⟩
  · rw [hget j]
    exact (Classical.choose_spec (hex j)).2.symm
  · rw [hget ⟨j, hj⟩]
    exact (Classical.choose_spec (hex ⟨j, hj⟩)).1

theorem q7Elt_acts :
    ActsBy q7Elt q7Cols := q7_cols ▸ actsBy_pow _ (word_conj_η_cols w7)

theorem q23Elt_acts :
    ActsBy q23Elt q23Cols := q23_cols ▸ actsBy_pow _ (word_conj_η_cols w23)

end CFSG.Sporadic.J4Schreier
