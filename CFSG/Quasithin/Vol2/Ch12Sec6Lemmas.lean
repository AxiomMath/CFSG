module

public import CFSG.Quasithin.Vol2.Ch12Sec6Frame
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Frame126Exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp126 G T L V →
    ∃ _ : IsMulCommutative ↥V, Nonempty (Frame126 T L V)

@[expose] def Concl12_6_1 (T L V : Subgroup G) [IsMulCommutative ↥V] (F : Frame126 T L V) :
    Prop :=
  (∀ u w : ↥V, F.β u ≠ 1 → F.β w ≠ 1 →
    ((∃ l ∈ L, ∃ hl : l ∈ Subgroup.normalizer (V : Set G),
        F.β ((conjAct V ⟨l, hl⟩ : MulAut ↥V) u) = F.β w) ↔
      (IsNonsing (F.β u) ↔ IsNonsing (F.β w)))) ∧
  (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
    Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 ∧
      V ⊓ Subgroup.centralizer (L : Set G) = V ⊓ Subgroup.centralizer (T : Set G)) ∧
  (thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ∨
    (V ⊔ (reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G))).relIndex
      (reducedAggregate (L ⊔ T)) ≤ 2) ∧
  (thompsonJ (Ri T L F.V1) = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ∧
    Subgroup.normalizer (Ri T L F.V1 : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
  oThreePrimeResidual (Subgroup.normalizer (L : Set G)) = L ∧
  (L = ⁅L, thompsonJ T⁆ → V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
    L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))

@[expose] def Lemma12_6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → Concl12_6_1 T L V F

@[expose] def Theorem12_6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V →
      ∀ v : G, F.Nonsing v → Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_6_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V →
      (∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹) ∧
      (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → ∀ v : G, F.Wt4 v →
        ¬ 2 ∣ (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G)).relIndex
          (Subgroup.centralizer ({v} : Set G)))

@[expose] def Concl12_6_20 (T L V : Subgroup G) [IsMulCommutative ↥V] (F : Frame126 T L V) :
    Prop :=
  (∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSubgroup V g ≠ ⊥ →
    (∀ x ∈ V ⊓ conjSubgroup V g, x ≠ 1 → F.Wt4 x) ∧
    Nat.card ↥(V ⊓ conjSubgroup V g) ≤ 8 ∧
    (∀ v ∈ V ⊓ conjSubgroup V g, ∃ c ∈ Subgroup.centralizer ({v} : Set G),
      conjSubgroup V g = conjSubgroup V c) ∧
    (⁅V, conjSubgroup V g⁆ ≠ ⊥ → ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g →
      V ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ Nat.card ↥(V ⊓ conjSubgroup V g) = 8 ∧
      autOn (conjSubgroup V g) V = pCoreOf 2
        (autOn (L ⊓ Subgroup.normalizer ((V ⊓ conjSubgroup V g : Subgroup G) : Set G)) V))) ∧
  3 ≤ E3.rParam V ∧ (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → 4 ≤ E3.rParam V)

@[expose] def Lemma12_6_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → Concl12_6_20 T L V F

@[expose] def Lemma12_6_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V →
      ∀ v : G, v ≠ 1 → F.Wt4 v →
        ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_6_22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (_ : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
      E3.wClos V 0 T ≤ Subgroup.centralizer (V : Set G) ∧
      (∀ g : G, E3.mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.normalizer (L : Set G)) ≤ 1 →
        conjSubgroup V g ≤ Subgroup.normalizer (V : Set G)) ∧
      1 < E3.wParam T V

@[expose] def Lemma12_6_23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V →
      V ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        V ⊓ quasithinOmegaOneCenter T = F.V1 ∧ Nat.card ↥F.V1 = 2

end CFSG.Quasithin.H13
