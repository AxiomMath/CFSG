module

public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type*} [Group G]

structure Hyp73 (V H E J : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  ti : IsTI V
  noncyclic : 2 < Nat.card V
  abelian : IsMulCommutative E
  le : E ≤ H
  normal : (E.subgroupOf H).Normal
  mem : V ∈ omegaSet V H E
  omega_le : ∀ W ∈ omegaSet V H E, W ≤ H
  iSub_le : iSub V H E ≤ J
  pcore_le : J ≤ pCoreOf 2 H
  jnormal : (J.subgroupOf H).Normal

structure Hyp711 (V H E : Subgroup G) : Prop extends Hyp73 V H E (pCoreOf 2 (kSub V H E)) where
  oddCore : fusionOddCoreOf (kSub V H E) = ⊥
  transitive : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k

structure IsBarMap (K N : Subgroup G) {X : Type} [Group X] (φ : ↥K →* X) : Prop where
  surjective : Function.Surjective φ
  ker_iff : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ N

@[expose] def barSub (K : Subgroup G) {X : Type} [Group X] (φ : ↥K →* X) (A : Subgroup G) :
    Subgroup X :=
  (A.subgroupOf K).map φ

@[expose] def barSet (K : Subgroup G) {X : Type} [Group X] (φ : ↥K →* X) (S : Set G) : Set X :=
  φ '' {k : ↥K | (k : G) ∈ S}

theorem mem_barSub {K A : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X} {x : X} :
    x ∈ barSub K φ A ↔ ∃ k : ↥K, (k : G) ∈ A ∧ φ k = x := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem mem_barSet {K : Subgroup G} {S : Set G} {X : Type} [Group X] {φ : ↥K →* X} {x : X} :
    x ∈ barSet K φ S ↔ ∃ k : ↥K, (k : G) ∈ S ∧ φ k = x :=
  Iff.rfl

@[expose] def IsSzGp (X : Type) [Group X] (n : ℕ) : Prop :=
  CFSG.Blueprint.SuzukiModel X 2 n

end CFSG.LocalAnalysis.WeakClosure81.SevenK
