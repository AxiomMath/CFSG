module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Chosen1647 (D : Data G) (V₀ V : Subgroup G) (z : G) : Prop :=
  ∃ g : G, InCalOStar 1 D.M V₀ V g ∧ z ∈ V ⊓ conjSubgroup V g

@[expose] def R16_47ch (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 →
      ∃ x : IntMod V hV, Setup1645 D V hV x ∧ Concl1647 V x.val ∧ Chosen1647 D V₀ V x.val

@[expose] def Concl1647aNe (D : Data G) (V₀ V : Subgroup G) (z : G) : Prop :=
  (⁅eTwo D V₀ z, eTwo D V₀ z⁆ = ⊥ ∧ ∀ e ∈ eTwo D V₀ z, e ^ 2 = 1) ∧
    (∀ h ∈ centralizer ({z} : Set G),
      conjSubgroup (uTwo D V₀ z) h = uTwo D V₀ z ∨
        uTwo D V₀ z ⊓ conjSubgroup (uTwo D V₀ z) h = ⊥) ∧
    ⁅V, eTwo D V₀ z⁆ ≤ uTwo D V₀ z

@[expose] def R16_47_ne_one (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 → V₀ ≠ ⊥ →
      ∀ x : IntMod V hV, Setup1645 D V hV x →
        IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) →
        Concl1647 V x.val → Chosen1647 D V₀ V x.val →
          V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G) ≤
            pCoreOf 2 (centralizer ({x.val} : Set G))

@[expose] def R16_47_ne_two (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 → V₀ ≠ ⊥ →
      ∀ x : IntMod V hV, Setup1645 D V hV x →
        IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) →
        Concl1647 V x.val → Chosen1647 D V₀ V x.val →
        V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G) ≤
          pCoreOf 2 (centralizer ({x.val} : Set G)) →
        ∀ h ∈ centralizer ({x.val} : Set G), V ≤ conjSubgroup D.M h →
          ¬ conjSubgroup V h ≤ D.M →
          conjSubgroup
              (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G))
              h ≤ F11.CTilde D.M V₀ V

@[expose] def R16_47_ne_gap (D : Data G) : Prop :=
  R16_47_ne_one D ∧ R16_47_ne_two D

@[expose] def R16_47_ne (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 → V₀ ≠ ⊥ →
      ∀ x : IntMod V hV, Setup1645 D V hV x →
        IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) →
        Concl1647 V x.val → Chosen1647 D V₀ V x.val → Concl1647aNe D V₀ V x.val

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
