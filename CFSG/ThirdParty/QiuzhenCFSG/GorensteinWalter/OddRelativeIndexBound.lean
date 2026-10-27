module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Small relative indices in odd groups -/

namespace CFSG.GorensteinWalter

universe u

/-- A relative index at most four inside an odd-order subgroup is at most
three. -/
public theorem odd_relIndex_le_three_of_le_four
    {G : Type u} [Group G] [Finite G]
    (H U : Subgroup G) (hUodd : Odd (Nat.card U))
    (hle : H.relIndex U ≤ 4) :
    H.relIndex U ≤ 3 := by
  have hodd : Odd (H.relIndex U) :=
    Odd.of_dvd_nat hUodd (Subgroup.relIndex_dvd_card H U)
  rcases hodd with ⟨k, hk⟩
  omega

end CFSG.GorensteinWalter
