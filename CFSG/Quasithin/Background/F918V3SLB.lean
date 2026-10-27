module

public import CFSG.Quasithin.Background.SmithB51SL3Lin

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

private noncomputable def elemSL (i j : Fin 3) (hij : i ≠ j) (c : K) : ↥(StatedSL 3 K) :=
  transv (Pi.single i c) (Pi.single j 1) (by
    rw [dotProduct_single, Pi.single_eq_of_ne hij, zero_mul])

private theorem slAct_elemSL (i j : Fin 3) (hij : i ≠ j) (c : K) (v : Fin 3 → K) :
    slAct (elemSL i j hij c) v = v + v j • Pi.single i c := by
  rw [elemSL, slAct_transv, single_dotProduct, one_mul]

theorem sl3_end_scalar (φ : (Fin 3 → K) →+ (Fin 3 → K))
    (h : ∀ (g : ↥(StatedSL 3 K)) (x : Fin 3 → K), φ (slAct g x) = slAct g (φ x)) :
    ∃ κ : K, ∀ x, φ x = κ • x := by
  have key : ∀ i j : Fin 3, i ≠ j → ∀ c : K,
      φ (Pi.single i c) = (φ (Pi.single j 1) j) • Pi.single i c := by
    intro i j hij c
    have h1 := h (elemSL i j hij c) (Pi.single j 1)
    rw [slAct_elemSL, slAct_elemSL, map_add, Pi.single_eq_same, one_smul] at h1
    exact add_left_cancel h1
  have hκ : ∀ i j : Fin 3, i ≠ j → φ (Pi.single i 1) i = φ (Pi.single j 1) j := by
    intro i j hij
    have := congrFun (key i j hij 1) i
    simpa using this
  refine ⟨φ (Pi.single 0 1) 0, fun x => ?_⟩
  set κ := φ (Pi.single 0 1) 0 with hκdef
  have hall : ∀ j : Fin 3, φ (Pi.single j 1) j = κ := by
    intro j
    fin_cases j
    · rfl
    · exact (hκ 0 1 (by decide)).symm
    · exact (hκ 0 2 (by decide)).symm
  have hsingle : ∀ (i : Fin 3) (c : K), φ (Pi.single i c) = κ • Pi.single i c := by
    intro i c
    obtain ⟨j, hji⟩ := exists_ne i
    rw [key i j hji.symm c, hall j]
  calc φ x = φ (∑ i, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, φ (Pi.single i (x i)) := map_sum _ _ _
    _ = ∑ i, κ • Pi.single i (x i) := Finset.sum_congr rfl fun i _ => hsingle i (x i)
    _ = κ • x := by rw [← Finset.smul_sum, Finset.univ_sum_single]

end B5

end CFSG.Quasithin
