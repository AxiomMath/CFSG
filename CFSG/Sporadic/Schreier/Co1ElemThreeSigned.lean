module

public import CFSG.Sporadic.Schreier.Co1ElemThreeData

public section

namespace CFSG.Sporadic.Co1Schreier

namespace ElemThree

theorem σMat_mul_σInvMat : ∀ i, σMat i * σInvMat i = 1 := by decide +kernel

theorem σInvMat_mul_σMat : ∀ i, σInvMat i * σMat i = 1 := by decide +kernel

@[expose] def σ (i : Fin 2) : GL (Fin 12) (ZMod 3) :=
  ⟨σMat i, σInvMat i, σMat_mul_σInvMat i, σInvMat_mul_σMat i⟩

@[expose] def Q : Subgroup (GL (Fin 12) (ZMod 3)) := Subgroup.closure {σ 0, σ 1, -1}

end ElemThree

end CFSG.Sporadic.Co1Schreier
