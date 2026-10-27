module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Ctx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P S126T2
open scoped IsMulCommutative

@[expose] def FactUv12617 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
    ∀ e : ↥(autOn (Kv ⊔ S) (Usec Kv S)) ≃* Equiv.Perm (Fin 8),
      ((autOn Kv (Usec Kv S)).subgroupOf (autOn (Kv ⊔ S) (Usec Kv S))).map e.toMonoidHom =
        alternatingGroup (Fin 8) →
      ((autOn (Rsec L Kv S v) (Usec Kv S)).subgroupOf (autOn (Kv ⊔ S) (Usec Kv S))).map
        e.toMonoidHom = Subgroup.zpowers (Equiv.swap 0 1) →
      ∃ w ∈ Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G),
        w ∉ Subgroup.centralizer (Kv : Set G)

end CFSG.Quasithin.H13
