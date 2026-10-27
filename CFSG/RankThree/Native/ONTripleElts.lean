module

public import CFSG.RankThree.Native.ONTripleModel

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

theorem gMArr_getD_of_ge {k : ℕ} (hk : 8 ≤ k) : gMArr.getD k 1 = 1 := by
  rw [gMArr, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  have hk' : ¬ k < 8 := by omega
  simp only [hk', dite_false, Option.getD_none]

theorem eM_mem (k : ℕ) : eM k ∈ M := by
  unfold eM regM
  refine runG_mem progM gMArr (fun j => ?_) k
  by_cases hj : j < 8
  · have e : gMArr.getD j 1 = gM ⟨j, hj⟩ := gMArr_getD ⟨j, hj⟩
    rw [e]
    exact gM_mem _
  · rw [gMArr_getD_of_ge (by omega)]
    exact M.one_mem

theorem eM_gen (k : Fin 8) : eM k.val = gM k := by
  unfold eM regM
  rw [runG_getD_lt _ _ (by rw [size_gMArr]; exact k.isLt), gMArr_getD]

abbrev zM : Mat45ˣ := gM 7

abbrev xM (i : Fin 4) : Mat45ˣ := eM (rX.getD i.val 0)

abbrev n1M : Mat45ˣ := eM rN1

abbrev n2M : Mat45ˣ := eM rN2

abbrev k1M : Mat45ˣ := eM rK1

abbrev k2M : Mat45ˣ := eM rK2

theorem zM_eq : eM 7 = zM := eM_gen 7

end CFSG.RankThree.Native.ONTriple
