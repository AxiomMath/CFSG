module

public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6Frame
public import CFSG.Quasithin.Vol2.Ch12Sec6Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace S126

@[expose] def InHz (T L V₁ H : Subgroup G) : Prop :=
  InH (L₁Of L V₁ ⊔ T) H ∧ ¬ H ≤ Subgroup.normalizer (L : Set G) ∧
    H ≤ Subgroup.centralizer (V₁ : Set G)

end S126

@[expose] def Concl12_6_24 (T L V : Subgroup G) [IsMulCommutative ↥V] (F : Frame126 T L V) :
    Prop :=
  (∀ W : Subgroup G, F.V1 ≤ W → W ≤ F.V5 →
    L₁Of L F.V1 ⊔ T ≤ Subgroup.normalizer (W : Set G) → W = F.V1 ∨ W = F.V5) ∧
  F.V5 ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ∧
  V ≤ pCoreOf 2 (Subgroup.normalizer (F.V2 : Set G)) ∧
  Subgroup.normalizer (F.V5 : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
  (∀ g : G, F.V1 < V ⊓ conjSubgroup V g → IsPGroup 2 ↥(V ⊔ conjSubgroup V g)) ∧
  (centralizerMod F.V1 ⊤ F.V5 = Subgroup.centralizer (V : Set G) ⊔ Ri T L F.V1 ∧
    Subgroup.centralizer (V : Set G) ⊔ Ri T L F.V1 =
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ Ri T L F.V1 ∧
    Subgroup.centralizer (F.V5 : Set G) = Subgroup.centralizer (V : Set G) ∧
    Subgroup.centralizer (V : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ∧
  ∀ H : Subgroup G, InHz T L F.V1 H →
    conjClosure F.V5 H ≤ pCoreOf 2 H ∧ HypF91 T V L F.V1 F.V5 H ∧
      pCoreOf 2 H = centralizerMod F.V1 H (conjClosure F.V5 H)

@[expose] def Lemma12_6_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      Concl12_6_24 T L V F

@[expose] def Lemma12_6_26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H : Subgroup G, InHz T L F.V1 H → IsMulCommutative ↥(conjClosure V H)

end CFSG.Quasithin.H13
