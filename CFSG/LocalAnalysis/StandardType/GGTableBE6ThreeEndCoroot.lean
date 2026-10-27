module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerRoots

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace E6ThreeEnd

open TableBExc.E6Three

local instance e6ThreeEndCorootNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def coverVec : Fin 6 → Fin Tag.E6.rank → ZMod 3 :=
  ![![0, 1, 0, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 2, 0, 2, 0, 0], ![0, 0, 1, 2, 1, 0],
    ![0, 1, 2, 1, 2, 0], ![0, 2, 2, 2, 2, 0]]

@[expose] def coverWord : Fin 6 → List (Fin Tag.E6.rank) :=
  ![[], [1], [1, 3, 2, 0, 4, 3, 2, 5, 4, 3], [1, 3], [1, 3, 2, 0, 4, 3, 2, 5, 4],
    [1, 3, 2, 0, 4, 3, 1, 2, 5, 4]]

theorem adWord_coverWord (k : Fin 6) :
    adWord .E6 3 (coverWord k) (coverVec k) =
      Pi.single (CFSG.SeitzReduction.highNode .E6) 1 := by
  revert k
  decide +kernel

theorem exists_cover_aux : ∀ c₀ c₁ c₂ c₃ c₄ c₅ : ZMod 3, ∃ k : Fin 6,
    c₀ * coverVec k 0 + c₁ * coverVec k 1 + c₂ * coverVec k 2 + c₃ * coverVec k 3 +
      c₄ * coverVec k 4 + c₅ * coverVec k 5 = 0 := by
  decide +kernel

theorem sum_eq_six (c x : Fin Tag.E6.rank → ZMod 3) :
    ∑ i, c i * x i =
      c 0 * x 0 + c 1 * x 1 + c 2 * x 2 + c 3 * x 3 + c 4 * x 4 + c 5 * x 5 := by
  change ∑ i : Fin 6, c i * x i = _
  rw [Fin.sum_univ_six]
  rfl

theorem exists_cover (c : Fin Tag.E6.rank → ZMod 3) :
    ∃ k : Fin 6, ∑ i, c i * coverVec k i = 0 := by
  obtain ⟨k, hk⟩ := exists_cover_aux (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
  exact ⟨k, by rw [sum_eq_six]; exact hk⟩

@[expose] def gVec : Fin 3 → Fin Tag.E6.rank → ZMod 3 :=
  ![![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 2, 1, 1]]

@[expose] def gWord : Fin 3 → List (Fin Tag.E6.rank) :=
  ![[], [], [1, 3, 2, 0, 4, 3, 1, 2, 3]]

theorem adWord_gWord (i : Fin 3) :
    adWord .E6 3 (gWord i) (gVec i) = Pi.single (CFSG.SeitzReduction.highNode .E6) 1 := by
  revert i
  decide +kernel

theorem adWord_wordE6G_gVec (i : Fin 3) : adWord .E6 3 (wordE6G i) (gVec i) = gVec i := by
  revert i
  decide +kernel

end E6ThreeEnd

end CFSG.StandardType
