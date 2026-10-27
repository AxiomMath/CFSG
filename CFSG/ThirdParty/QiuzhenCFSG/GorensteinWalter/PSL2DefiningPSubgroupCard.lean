module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- The order of every defining-characteristic subgroup of `PSL₂(K)`
divides the field cardinality. -/
public theorem psl2_defining_pgroup_card_dvd_field
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (N : Subgroup (PSL2MatrixGroup K)) (hN : IsPGroup p N) :
    Nat.card N ∣ Nat.card K := by
  obtain ⟨S, hNS⟩ := hN.exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := psl2UpperUnipotent_isSylow K hKcard
  have hScard : Nat.card (S : Subgroup (PSL2MatrixGroup K)) = Nat.card K := by
    calc
      Nat.card (S : Subgroup (PSL2MatrixGroup K)) =
          Nat.card (S₀ : Subgroup (PSL2MatrixGroup K)) := by
        exact Nat.card_congr (Sylow.equiv S S₀).toEquiv
      _ = Nat.card (psl2UpperUnipotentSubgroup K) := by rw [hS₀]
      _ = Nat.card K := psl2UpperUnipotentSubgroup_card K
  apply dvd_trans (Subgroup.card_dvd_of_le hNS)
  rw [hScard]

end CFSG.GorensteinWalter
