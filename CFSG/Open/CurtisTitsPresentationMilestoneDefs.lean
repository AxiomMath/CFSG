module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open scoped MatrixGroups

@[expose] def curtisTitsLevi (m : ℕ) (F : Type) [Field F] (J : Finset (Fin m)) : Subgroup SL(m + 1, F) :=
  Subgroup.closure {A | ∃ k ∈ J, ∃ c : F,
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.transvection k.castSucc k.succ c ∨
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.transvection k.succ k.castSucc c}

end CFSG.Open
