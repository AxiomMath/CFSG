module

public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {H U L N : Subgroup G} {m : ℕ}

theorem l2_pow_sq_le_relIndex_centralizer (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hU : IsPGroup 2 U) (hUH : U ≤ H) {c : ℕ}
    (hser : IsChiefSeriesFrom H U U c) {t : G} (htH : t ∈ H)
    (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    (2 ^ m) ^ c ≤
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex U := by
  have hk : ∀ L' N' : Subgroup G, IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      2 ^ m ≤ (centralizerMod L' N' (Subgroup.zpowers t)).relIndex N' := by
    intro L' N' hstep' hnc'
    exact l2ChiefSectionRep_pow_le_relIndex_centralizerMod hm2 hL2 hU hUH hstep' hnc'
      htH ht htO
  exact CFSG.Quasithin.D15Proof.pow_le_relIndex hUH (Subgroup.zpowers_le.mpr htH) hk hser

end CFSG.Quasithin.Stroth
