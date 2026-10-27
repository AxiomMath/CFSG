module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow structure across odd-index subgroups

A Sylow `2`-subgroup of an odd-index subgroup is already Sylow in the ambient
finite group.  This module packages the resulting transfer for the
Gorenstein--Walter dihedral-Sylow predicate.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Dihedral Sylow `2`-subgroups transfer from a subgroup of odd index to the
ambient finite group. -/
public theorem hasDihedralSylowTwo_of_odd_index
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hindex : Odd H.index)
    (hH : HasDihedralSylowTwo H) :
    HasDihedralSylowTwo G := by
  classical
  let P : Sylow 2 H := Classical.choice Sylow.nonempty
  let T : Subgroup G := (P : Subgroup H).map H.subtype
  have hTp : IsPGroup 2 T := P.isPGroup'.map H.subtype
  have hTindex : ¬ 2 ∣ T.index := by
    change ¬ 2 ∣ ((P : Subgroup H).map H.subtype).index
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two
      P.not_dvd_index hindex.not_two_dvd_nat
  let T' : Sylow 2 G := hTp.toSylow hTindex
  have ePT : P ≃* T :=
    Subgroup.equivMapOfInjective (P : Subgroup H) H.subtype
      H.subtype_injective
  rcases hH P with ⟨m, hm, ⟨ePD⟩⟩
  intro S
  refine ⟨m, hm, ⟨?_⟩⟩
  have eTPD : T' ≃* DihedralGroup (2 ^ m) := by
    change T ≃* DihedralGroup (2 ^ m)
    exact ePT.symm.trans ePD
  exact (Sylow.equiv S T').trans eTPD

end CFSG.GorensteinWalter
