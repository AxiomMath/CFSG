module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def J4OutTrivial : Prop :=
  ∀ (X : Type) [Group X], IsSporadic .J4 X → ∀ φ : MulAut X, ∃ x : X, ∀ y, φ y = x * y * x⁻¹

@[expose] def J4BlockFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSporadic .J4 K → ∀ B : Subgroup K, IsShort2 B →
    (IsExt ↥B (fun N _ => IsE2 11 N) (fun Y _ => IsSporadic .M24 Y) ∨
      IsExt ↥B (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y)) →
    Subgroup.normalizer (B : Set K) = B ∧
      Subgroup.centralizer (pCoreOf 2 B : Set K) = pCoreOf 2 B ∧
      (∀ W : Subgroup K, W ≤ pCoreOf 2 B → B ≤ Subgroup.normalizer (W : Set K) →
        W = ⊥ ∨ W = pCoreOf 2 B) ∧
      ∃ x : K, x ∈ B ∧ orderOf x = 3 ∧
        pCoreOf 2 B ⊓ Subgroup.centralizer ({x} : Set K) ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(perfectCore (Subgroup.centralizer ({x} : Set K))) ∧
        Nat.card ↥(Subgroup.center ↥(perfectCore (Subgroup.centralizer ({x} : Set K)))) = 6 ∧
        IsSporadic .M22 (↥(perfectCore (Subgroup.centralizer ({x} : Set K))) ⧸
          Subgroup.center ↥(perfectCore (Subgroup.centralizer ({x} : Set K)))) ∧
        ¬ pCoreOf 2 B ⊓ Subgroup.centralizer ({x} : Set K) ≤
          Subgroup.centralizer (perfectCore (Subgroup.centralizer ({x} : Set K)) : Set K)

@[expose] def InspBM22Cover : Prop :=
  ∀ (Yh : Type) [Group Yh] [Finite Yh] (Y : Subgroup Yh) (r : Yh), Y.Normal →
    CFSG.IsQuasisimple ↥Y → IsQuasithin ↥Y → CFSG.SectionRank.IsKGroupCat ↥Y →
    r ^ 2 = 1 → ¬ Y ≤ Subgroup.centralizer ({r} : Set Yh) →
    ∀ C : Subgroup Yh, C ≤ Y ⊓ Subgroup.centralizer ({r} : Set Yh) →
      (C.subgroupOf (Y ⊓ Subgroup.centralizer ({r} : Set Yh))).IsSubnormal →
      CFSG.IsQuasisimple ↥C → ¬ IsSporadic .M22 (↥C ⧸ Subgroup.center ↥C)

end CFSG.Quasithin.H13.Ch4
