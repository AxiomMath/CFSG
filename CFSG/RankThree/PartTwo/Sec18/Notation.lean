module

public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type*} [Group G]

@[expose] def fourChar (S : Subgroup G) : Fin 4 → Subgroup G
  | 0 => (CFSG.omegaOneCenter (⊤ : Subgroup S)).map S.subtype
  | 1 => (CFSG.higherElemThompson S 0).map S.subtype
  | 2 => (CFSG.higherElemThompsonOmega S 1).map S.subtype
  | 3 => (CFSG.higherElemThompsonOmega S 2).map S.subtype

@[expose] def ThreeOfFourNormal (H : Subgroup G) (T : Fin 4 → Subgroup G) : Prop :=
  ∀ i j : Fin 4, i ≠ j → H ≤ Subgroup.normalizer (T i : Set G) ∨
    H ≤ Subgroup.normalizer (T j : Set G)

@[expose] def InducesInnerMod (x : G) (K Y : Subgroup G) : Prop :=
  x ∈ Subgroup.normalizer (K : Set G) ∧
    ∃ k ∈ K, ∀ y ∈ K, x * y * x⁻¹ * (k * y * k⁻¹)⁻¹ ∈ Y

@[expose] def conjugatesIn (F P : Subgroup G) : Set (Subgroup G) :=
  {F' | (∃ g : G, F' = F.map (MulAut.conj g).toMonoidHom) ∧ F' ≤ P}

theorem mem_conjugatesIn_iff {F P F' : Subgroup G} :
    F' ∈ conjugatesIn F P ↔ (∃ g : G, F' = F.map (MulAut.conj g).toMonoidHom) ∧ F' ≤ P :=
  Iff.rfl

@[expose] def omegaOneThree (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ P ∧ x ^ 3 = 1}

@[expose] def IsZ3TimesHeis {G : Type} [Group G] (X : Subgroup G) : Prop :=
  ∃ U V : Subgroup G, U ⊔ V = X ∧ U ⊓ V = ⊥ ∧ Nat.card U = 3 ∧ Sec4.IsHeisThree V ∧
    U ≤ Subgroup.centralizer (V : Set G)

@[expose] def HasSectionalThreeRankThree (P : Subgroup G) : Prop :=
  (∀ (U V : Subgroup G) [(V.subgroupOf U).Normal], U ≤ P →
      IsElementaryAbelian 3 (U ⧸ V.subgroupOf U) → Nat.card (U ⧸ V.subgroupOf U) ≤ 27) ∧
    ∃ (U V : Subgroup G) (_ : (V.subgroupOf U).Normal), U ≤ P ∧
      IsElementaryAbelian 3 (U ⧸ V.subgroupOf U) ∧ Nat.card (U ⧸ V.subgroupOf U) = 27

@[expose] def IsMaxParabolicRankTwo {Y : Type*} [Group Y] (X : Subgroup Y) : Prop :=
  IsCoatom X ∧ ∃ T : Sylow 2 Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ X

structure Sec18H (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) : Prop
    extends Sec18Std G A M where
  mem_scriptH : H ∈ scriptH A M
  centralizer_eq : sectionCentralizer A (inSubgroup perfectResidual H)
      (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) = (Subgroup.zpowers c : Set G)

end CFSG.RankThree.PartTwo.Sec18
