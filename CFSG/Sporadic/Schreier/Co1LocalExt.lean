module

public import CFSG.Sporadic.Schreier.Co1LocalExtData
public import CFSG.Sporadic.Schreier.Co1SplitLocal

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree

@[expose] noncomputable def locWord (w : List ℕ × List ℕ) : GL24 :=
  eProd (Native.expVec w.1) * wordG [c 0, c 1, r] (w.2.map Int.ofNat)

@[expose] noncomputable def extH (i : Fin 3) : GL24 := locWord (Data.witLeft.getD i.val ([], []))

@[expose] noncomputable def extK (i : Fin 3) : GL24 := locWord (Data.witConj.getD i.val ([], []))

theorem locWord_mem (w : List ℕ × List ℕ) : locWord w ∈ A := by
  refine A.mul_mem (E_le_A (eProd_mem _)) (wordG_mem (fun g hg => ?_) _)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact c_mem_A 0
  · exact c_mem_A 1
  · exact r_mem_A

@[expose] noncomputable def extInit : List GL24 :=
  [a 0, a 1, a 2, a 3, a 4, a 5, c 0, c 1, r, ThreeLocal.x]

@[expose] noncomputable def extL : List GL24 := dagG extInit Data.genDerivs

@[expose] noncomputable def extM : Subgroup GL24 := Subgroup.closure {g | g ∈ extInit}

end CFSG.Sporadic.Co1Schreier
