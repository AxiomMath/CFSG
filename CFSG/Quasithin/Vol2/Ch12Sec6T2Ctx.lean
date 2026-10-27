module

public import CFSG.Quasithin.Vol2.Ch12Sec6FrE

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P
open scoped IsMulCommutative

namespace S126T2

variable {G : Type} [Group G]

@[expose] def Gv (v : G) : Subgroup G := Subgroup.centralizer ({v} : Set G)

@[expose] def Tv (T : Subgroup G) (v : G) : Subgroup G := T ⊓ Gv v

@[expose] def Lv (L : Subgroup G) (v : G) : Subgroup G := perfectCore (L ⊓ Gv v)

@[expose] def Rv (T L : Subgroup G) (v : G) : Subgroup G := pCoreOf 2 ((L ⊔ T) ⊓ Gv v)

@[expose] def Vv (L V : Subgroup G) (v : G) : Subgroup G := ⁅V, Lv L v⁆

@[expose] def Qv (T V : Subgroup G) : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G)

@[expose] def Rsec (L Kv S : Subgroup G) (v : G) : Subgroup G :=
  centralizerSection S (Lv L v ⊔ pCoreOf 2 (Kv ⊔ S)) (pCoreOf 2 (Lv L v ⊔ pCoreOf 2 (Kv ⊔ S)))

@[expose] def Usec (Kv S : Subgroup G) : Subgroup G := quasithinOmegaOneCenter (pCoreOf 2 (Kv ⊔ S))

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] def WtTwo (F : Frame126 T L V) (v : G) : Prop :=
  ∃ (E : S126FE.Frame126E F) (hv : v ∈ V), wt ((E.γ ⟨v, hv⟩ : ↥(coreMod 8)) : PermMod 8) = 2

@[expose] def Delta (F : Frame126 T L V) (v : G) : Set G :=
  {u | ∃ hu : u ∈ V, u ∈ Vv L V v ∧ ∃ i j : Fin 8, 2 ≤ i.val ∧ 2 ≤ j.val ∧ i ≠ j ∧
    F.β ⟨u, hu⟩ = QuotientGroup.mk (pe i j)}

structure Ctx1262 [Finite G] (F : Frame126 T L V) (v : G) (Kv S : Subgroup G) : Prop where
  hyp : Hyp126 G T L V
  mem : v ∈ V
  coord : F.β ⟨v, mem⟩ = QuotientGroup.mk (pe 0 1)
  not_le : ¬ Gv v ≤ Subgroup.normalizer (L : Set G)
  choice : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
    (∃ u : G, WtTwo F u ∧ ¬ Gv u ≤ Subgroup.normalizer (L : Set G)) → WtTwo F v
  cComp : Kv ∈ cComp (Gv v)
  lv_le : Lv L v ≤ Kv
  kv_eq : Kv = oThreePrimeResidual (perfectCore (Gv v))
  normal : Gv v ≤ Subgroup.normalizer (Kv : Set G)
  quasisimple : CFSG.IsQuasisimple (↥Kv ⧸ CFSG.pCore 2 ↥Kv)
  sylow : CFSG.QuasithinUnique.IsSylowTwoOf S (Gv v)
  tv_le : Tv T v ≤ S
  sylowN : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ Subgroup.normalizer (Lv L v : Set G))
    (Gv v ⊓ Subgroup.normalizer (Lv L v : Set G))

end S126T2

end CFSG.Quasithin.H13
