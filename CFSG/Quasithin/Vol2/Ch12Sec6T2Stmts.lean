module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Ctx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P S126T2
open scoped IsMulCommutative

@[expose] def Lemma12_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → ∀ (v : G) (hv : v ∈ V),
      F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) →
      ∃ Kv : Subgroup G, Kv ∈ cComp (Gv v) ∧ Lv L v ≤ Kv ∧
        Kv = oThreePrimeResidual (perfectCore (Gv v)) ∧
        Gv v ≤ Subgroup.normalizer (Kv : Set G) ∧ CFSG.IsQuasisimple (↥Kv ⧸ CFSG.pCore 2 ↥Kv)

@[expose] def Lemma12_6_4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      CFSG.QuasithinUnique.IsSylowTwoOf (Rsec L Kv S v)
        (centralizerSection (Kv ⊔ S) (Lv L v ⊔ pCoreOf 2 (Kv ⊔ S))
          (pCoreOf 2 (Lv L v ⊔ pCoreOf 2 (Kv ⊔ S)))) ∧
      Rv T L v = Rsec L Kv S v ⊓ Tv T v ∧
      (Tv T v).relIndex S ≤ (Tv T v).relIndex T ∧ (Tv T v).relIndex T = 4 ∧
      (Rv T L v).relIndex (Rsec L Kv S v) ≤ 4 ∧ pCoreOf 2 (Kv ⊔ S) ≤ Rsec L Kv S v ∧
      Rsec L Kv S v ≤ Subgroup.normalizer (Lv L v : Set G) ∧
      ⁅Lv L v, Rsec L Kv S v⁆ ≤ pCoreOf 2 (Lv L v) ∧
      Rsec L Kv S v = centralizerSection S (Lv L v) (pCoreOf 2 (Lv L v))

@[expose] def Lemma12_6_6_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      (¬ thompsonJ T ≤ Qv T V → Lv L v = ⁅Lv L v, thompsonJ (Tv T v)⁆ ∨
        thompsonJ (Tv T v) = thompsonJ (Qv T V)) ∧
      (thompsonJ T ≤ Qv T V → thompsonJ T = thompsonJ (Qv T V) ∧
        thompsonJ (Qv T V) = thompsonJ (Tv T v)) ∧
      (Lv L v = ⁅Lv L v, thompsonJ (Tv T v)⁆ → L = ⁅L, thompsonJ T⁆) ∧
      (thompsonJ (Tv T v) ≤ Qv T V → S = Tv T v ∧ Rsec L Kv S v = Rv T L v ∧
        thompsonJ (Tv T v) = thompsonJ (Rv T L v) ∧ thompsonJ (Rv T L v) = thompsonJ (Qv T V) ∧
        Subgroup.normalizer (thompsonJ S : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (¬ thompsonJ (Tv T v) ≤ Qv T V → ¬ thompsonJ T ≤ Qv T V ∧
        Lv L v = ⁅Lv L v, thompsonJ (Tv T v)⁆)

@[expose] def Lemma12_6_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      Lv L v < Kv ∧ ¬ Kv ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_6_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      ¬ CFSG.IsQuasisimple ↥Kv

@[expose] def Lemma12_6_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      (CFSG.QuasithinUnique.CharTwo (Kv ⊔ S) ∧
        pCoreOf 2 (Kv ⊔ S) = (Kv ⊔ S) ⊓ Subgroup.centralizer (Usec Kv S : Set G)) ∧
      (∃ _ : ((pCoreOf 2 (Kv ⊔ S)).subgroupOf Kv).Normal,
        IsSimpleGroup (↥Kv ⧸ (pCoreOf 2 (Kv ⊔ S)).subgroupOf Kv)) ∧
      Vv L V v ≤ ⁅Usec Kv S, Kv⁆

@[expose] def Lemma12_6_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      ¬ thompsonJ (Tv T v) ≤ Qv T V

@[expose] def Lemma12_6_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      ∃ hU : IsElemAbelian 2 (Usec Kv S), IsFFModule (autI hU (Kv ⊔ S))

@[expose] def Lemma12_6_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
        ¬ Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
          ¬ IsAltBlockType L 8

@[expose] def Lemma12_6_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      ¬ Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_6_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
      IsAltBlockType L 8 ∧ IsAltBlockType Kv 7 ∧ V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧
        L ⊔ T = L ⊔ Rv T L v

@[expose] def Final1262 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S → False

end CFSG.Quasithin.H13
