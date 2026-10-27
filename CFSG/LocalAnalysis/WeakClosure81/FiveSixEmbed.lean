module

public import CFSG.Quasithin.Background.SimsD1TransGrp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin Equiv

variable {G : Type} [Group G] [Finite G]

theorem ncard_maxOver_map_subgroupOf {H T : Subgroup G} (hTH : T ≤ H) {Q : Type*} [Group Q]
    (ι : ↥H →* Q) (hι : Function.Injective ι) :
    (maxOver ((⊤ : Subgroup ↥H).map ι) ((T.subgroupOf H).map ι)).ncard = (maxOver H T).ncard := by
  have h1 := CFSG.Quasithin.SimsD1.TransGrp.maxOver_map_eq ι hι ⊤ (T.subgroupOf H)
  have h2 := CFSG.Quasithin.SimsD1.TransGrp.maxOver_map_eq H.subtype H.subtype_injective ⊤
    (T.subgroupOf H)
  rw [Subgroup.map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    at h2
  rw [h1, Set.ncard_image_of_injective _ (Subgroup.map_injective hι), h2,
    Set.ncard_image_of_injective _ (Subgroup.map_injective H.subtype_injective)]

end CFSG.LocalAnalysis.WeakClosure81
