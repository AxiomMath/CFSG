module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Ctx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P S126T2
open scoped IsMulCommutative

@[expose] def FactUv12618 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
    (IsAlt 7 ↥(autOn Kv (Usec Kv S)) ∨ IsAlt 8 ↥(autOn Kv (Usec Kv S))) →
      ∃ w ∈ Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G),
        w ∉ Subgroup.centralizer (Kv : Set G)

@[expose] def BlockL12618 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
    ¬ Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G) →
      IsAltBlockType L 8

@[expose] def BlockKv12618 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
    IsAltBlockType L 8 → IsAlt 7 ↥(autOn Kv (Usec Kv S)) → IsAltBlockType Kv 7

end CFSG.Quasithin.H13
