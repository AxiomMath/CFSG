module

public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofBFix

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Step155W315x (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → CFSG.Open.pCoreOf 2 Y ≤ P → w155 A M X ≠ ⊥ →
      w155 A M X = delta A (lB A) (w155 A M X) ∧
        (w155 A M X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∨
          Hyp315 (CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X) (CFSG.Open.pCoreOf 2 Y) ∨
          ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ CFSG.Open.pCoreOf 2 Y ∧
            (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic ∧
            w155 A M X ≤ Subgroup.normalizer (C : Set G))

@[expose] noncomputable def Step155W315P (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → CFSG.Open.pCoreOf 2 Y ≤ P →
      ¬ w155 A M X ≤ pPrimeCoreOf 3 M →
        w155 A M X = delta A (lB A) (w155 A M X) ∧
          (w155 A M X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∨
            Hyp315 (CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X) (CFSG.Open.pCoreOf 2 Y) ∨
            ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ CFSG.Open.pCoreOf 2 Y ∧
              (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic ∧
              w155 A M X ≤ Subgroup.normalizer (C : Set G))

@[expose] noncomputable def Step155W315xR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155W315x A c L

@[expose] noncomputable def Step155W315PR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155W315P A c L

end CFSG.RankThree.PartTwo.Sec15
