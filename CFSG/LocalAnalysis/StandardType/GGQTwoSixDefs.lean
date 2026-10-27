module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockHubDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointSu
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointRels

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

@[expose] def qTwoSixWinEmb {m k i : ℕ} (h : i + k ≤ m) : Fin k ↪ Fin m where
  toFun a := ⟨a.val + i, by have := a.isLt; omega⟩
  inj' a b hab := Fin.ext (by simpa using congrArg Fin.val hab)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {H : Subgroup G}

@[expose] def QTwoFourChart (B : QTwoCanonBlocks K 5 6 H) (s : ℕ) (hs : s + 4 ≤ 6) (φ : Su K 2 1 4 →* G) : Prop :=
  Function.Injective φ ∧
    ∀ J : Finset (Fin 4), 2 ≤ J.card → B.blk (J.map (qTwoSixWinEmb hs)) = (coordBlockSU K 2 1 J).map φ

end CFSG.StandardType.QTwo.SixPoint

end
