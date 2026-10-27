module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- Theorem 2.6's equality `U = O(Ĥ)` identifies `F(U)` with the odd part
of `F(Ĥ)`, and hence embeds it in `F(Ĥ)`. -/
public theorem FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h26 : CentralizerStructure c) :
    c.FU ≤ fittingSubgroupOf c.Hhat := by
  have hFUeq :
      c.FU = piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} := by
    calc
      c.FU = fittingSubgroupOf c.U := rfl
      _ = fittingSubgroupOf (oddCoreOf c.Hhat) := by rw [h26.1]
      _ = piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} :=
        fittingSubgroupOf_oddCore_eq_oddPart_fittingSubgroupOf c.Hhat
  rw [hFUeq]
  exact piCoreOf_le _ _

end CFSG.GorensteinWalter
