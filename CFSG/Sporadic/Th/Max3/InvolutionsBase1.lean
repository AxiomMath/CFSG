
module


public import CFSG.Sporadic.Th.Max3.RelationsBase1

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

namespace InvRep

@[expose] noncomputable def genM : Gen → ↥M
  | .x => ⟨x, x_mem_M⟩
  | .y => ⟨y, y_mem_M⟩

@[expose] noncomputable def wordM
    (w : List Gen) : ↥M := ⟨wordProd w, wordProd_mem_M w⟩

theorem wordM_nil : wordM [] = 1 := Subtype.ext rfl

theorem wordM_cons
    (l : Gen) (w : List Gen) : wordM (l :: w) = genM l * wordM w :=
  Subtype.ext (by cases l <;> rfl)

end InvRep

end CFSG.Sporadic.Th.Max3
