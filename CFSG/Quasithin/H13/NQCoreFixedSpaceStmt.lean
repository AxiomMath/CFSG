module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.Campbell (elemThompsonIn)

@[expose] def StmtCoreContainedAtMostOneNoncentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G),
    Group.IsSolvable ↥H → IsSylowTwoOf T H → ¬ (T.subgroupOf H).Normal →
    M < H → (∀ Y : Subgroup G, M < Y → Y ≤ H → Y = H) → T ≤ M →
    (∀ Y : Subgroup G, Y < H → (∀ Z : Subgroup G, Y < Z → Z ≤ H → Z = H) → T ≤ Y → Y = M) →
    V ≤ T → T ≤ normalizer (V : Set G) → IsElemAbelian 2 V → V ≠ ⊥ →
    V ≤ (CFSG.pCore 2 ↥H).map H.subtype →
    IsElemAbelian 2 (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom) →
    (∀ E : Subgroup (MulAut ↥V), (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹) →
      E ≠ ⊥ → IsElementaryAbelian 2 ↥E →
        Nat.card ↥E ^ 2 * Nat.card ↥(FixedPoints.subgroup ↥E ↥V) < Nat.card ↥V) →
    ¬ elemThompsonIn 2 T ≤ (CFSG.pCore 2 ↥H).map H.subtype →
    ∀ n : ℕ, IsChiefSeriesFrom H (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom)
      (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom) n → n ≤ 1

@[expose] def StmtCoreContainedAtLeastTwoNoncentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G →
    CFSG.Assembly.evenRank G ≤ 2 → ∀ (F H T M V R : Subgroup G), quasithinIsSylowTwo T →
    T ≤ F → T ≤ H → Group.IsSolvable ↥H → CharTwo H → ¬ (T.subgroupOf H).Normal →
    M < H → (∀ Y : Subgroup G, M < Y → Y ≤ H → Y = H) → T ≤ M →
    (∀ Y : Subgroup G, Y < H → (∀ Z : Subgroup G, Y < Z → Z ≤ H → Z = H) → T ≤ Y → Y = M) →
    V ≤ F → (V.subgroupOf F).Normal → IsElemAbelian 2 V → V ≠ ⊥ →
    V ≤ (CFSG.pCore 2 ↥H).map H.subtype → R = T ⊓ centralizer (V : Set G) →
    (R.subgroupOf F).Normal →
    (∀ X : Subgroup G, X ≤ R → X ≠ ⊥ → ¬ (X.subgroupOf (F ⊔ H)).Normal) →
    (∀ E : Subgroup (MulAut ↥V), (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹) →
      E ≠ ⊥ → IsElementaryAbelian 2 ↥E →
        Nat.card ↥E * Nat.card ↥(FixedPoints.subgroup ↥E ↥V) < Nat.card ↥V ∧
        Nat.card ↥E * Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
          ∀ σ ∈ E, ∀ v, φ (σ v) = φ v} < Nat.card (↥V →* Multiplicative (ZMod 2))) →
    IsElemAbelian 2 (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom) →
    ∀ n : ℕ, IsChiefSeriesFrom H (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom)
      (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom) n → 2 ≤ n

end CFSG.Quasithin.H13.NQCore
