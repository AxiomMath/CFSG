module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.Quasithin.CT

open CFSG.QuasithinUnique

open CFSG.Open

section Transport

variable {G : Type*} [Group G]

theorem charTwo_iff_internal {H : Subgroup G} :
    CharTwo H ↔ Subgroup.centralizer (CFSG.Open.pCore 2 H : Set H) ≤ CFSG.Open.pCore 2 H :=
  CFSG.QuasithinUnique.charTwo_iff_internal

theorem charTwo_map_subtype {K : Subgroup G} {L : Subgroup K}
    (h : Subgroup.centralizer (CFSG.Open.pCore 2 L : Set L) ≤ CFSG.Open.pCore 2 L) :
    CharTwo (L.map K.subtype) := CFSG.QuasithinUnique.charTwo_map_subtype h

theorem map_subtype_normalizer {K X : Subgroup G} (hXK : X ≤ K) :
    (Subgroup.normalizer ((X.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      K ⊓ Subgroup.normalizer (X : Set G) := CFSG.QuasithinUnique.map_subtype_normalizer hXK

theorem map_subtype_centralizer {K X : Subgroup G} (hXK : X ≤ K) :
    (Subgroup.centralizer ((X.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer (X : Set G) := CFSG.QuasithinUnique.map_subtype_centralizer hXK

end Transport

variable {G : Type*} [Group G] [Finite G]

theorem CharTwo.of_normal {H K : Subgroup G} (hK : CharTwo K) (hHK : H ≤ K)
    (hn : (H.subgroupOf K).Normal) : CharTwo H := CFSG.QuasithinUnique.CharTwo.of_normal hK hHK hn

theorem CharTwo.inf_normalizer {K X : Subgroup G} (hK : CharTwo K) (hXK : X ≤ K)
    (hX : IsPGroup 2 X) : CharTwo (K ⊓ Subgroup.normalizer (X : Set G)) :=
  CFSG.QuasithinUnique.CharTwo.inf_normalizer hK hXK hX

theorem CharTwo.inf_centralizer {K X : Subgroup G} (hK : CharTwo K) (hXK : X ≤ K)
    (hX : IsPGroup 2 X) : CharTwo (K ⊓ Subgroup.centralizer (X : Set G)) :=
  CFSG.QuasithinUnique.CharTwo.inf_centralizer hK hXK hX

theorem charTwo_normalizer_of_le {U V : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V)
    (hU : CharTwo (Subgroup.normalizer (U : Set G))) :
    CharTwo (Subgroup.normalizer (V : Set G)) :=
  CFSG.QuasithinUnique.charTwo_normalizer_of_le hV hUV hU

theorem charTwo_normalizer_of_inf_center
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T D : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hD : IsPGroup 2 D)
    (hDZ : D ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥) :
    CharTwo (Subgroup.normalizer (D : Set G)) :=
  CFSG.QuasithinUnique.charTwo_normalizer_of_inf_center hev hT hD hDZ

end CFSG.Quasithin.CT
