module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def perfInter890 {G : Type} [Group G] (J X : Subgroup G) : Subgroup G :=
  (CFSG.perfectResidual ↥(J ⊓ X)).map (J ⊓ X).subtype

@[expose] def oddCore890 {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  (CFSG.oddCore ↥H).map H.subtype

structure Cfg890 {G : Type} [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ) :
    Prop where
  set880 : Set880 D L P
  normal_L : D.M ≤ normalizer (L : Set G)
  memJ : J ∈ calC D.M
  normal_J : D.M ≤ normalizer (J : Set G)
  le_cent : J ≤ F08.CentOverO2 D.M L
  szJ : IsSz (Bar2 J) n
  le_P : Y ≤ P
  card_Y : Nat.card Y = 3
  ne_Z : Y ≠ ZOf (P ⊓ L)

@[expose] def J2OrderThree_890 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .J2 → ∀ A B : Subgroup X, Nat.card A = 3 →
    Nat.card B = 3 → (Nat.card (centralizer (A : Set X))).factorization 3 ≠ 2 →
    (Nat.card (centralizer (B : Set X))).factorization 3 ≠ 2 →
    ∃ x : X, B = A.map (MulAut.conj x).toMonoidHom

@[expose] def J2ThreeBFix_890 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .J2 → ∀ y : X, orderOf y = 3 →
    (Nat.card (centralizer ({y} : Set X))).factorization 3 = 2 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (ρ : X →* (V ≃ₗ[ZMod 2] V)), Nontrivial V →
      (∀ W : Submodule (ZMod 2) V, (∀ x : X, W.map (ρ x : V →ₗ[ZMod 2] V) ≤ W) → W = ⊥ ∨ W = ⊤) →
      ∃ v : V, v ≠ 0 ∧ ρ y v = v

structure LJChief_890 {G : Type} [Group G] (L J A B : Subgroup G) : Prop where
  le : B ≤ A
  ne : B ≠ A
  le_core : A ≤ pCoreOf 2 J
  normA_L : L ≤ normalizer (A : Set G)
  normA_J : J ≤ normalizer (A : Set G)
  normB_L : L ≤ normalizer (B : Set G)
  normB_J : J ≤ normalizer (B : Set G)
  comm_le : ⁅A, A⁆ ≤ B
  sq_mem : ∀ a ∈ A, a ^ 2 ∈ B
  minimal : ∀ C : Subgroup G, B ≤ C → C ≤ A → L ≤ normalizer (C : Set G) →
    J ≤ normalizer (C : Set G) → C = B ∨ C = A

@[expose] def barImg_890 {G : Type} [Group G] (L Y : Subgroup G) : Subgroup (Bar2 L) :=
  (Y.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

@[expose] def IsMaxKInv_890 {G : Type} [Group G] (K H R : Subgroup G) : Prop :=
  R ≤ H ∧ IsPGroup 2 R ∧ K ≤ normalizer (R : Set G) ∧
    ∀ R' : Subgroup G, R ≤ R' → R' ≤ H → IsPGroup 2 R' → K ≤ normalizer (R' : Set G) → R' = R

@[expose] def KPair_890 {G : Type} [Group G] [Finite G] (D : Data G) (K N R : Subgroup G) :
    Prop :=
  N ∈ calMOf K ∧ N ≠ D.M ∧ R ≤ N ⊓ D.M ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧ K ≤ normalizer (R : Set G)

theorem r890_perfInter_le_inf {G : Type} [Group G] (J X : Subgroup G) :
    perfInter890 J X ≤ J ⊓ X :=
  Subgroup.map_subtype_le _

theorem r890_perfInter_le_left {G : Type} [Group G] (J X : Subgroup G) :
    perfInter890 J X ≤ J :=
  (r890_perfInter_le_inf J X).trans inf_le_left

theorem r890_perfInter_le_right {G : Type} [Group G] (J X : Subgroup G) :
    perfInter890 J X ≤ X :=
  (r890_perfInter_le_inf J X).trans inf_le_right

theorem r890_perfInter_perfect {G : Type} [Group G] [Finite G] (J X : Subgroup G) :
    ⁅perfInter890 J X, perfInter890 J X⁆ = perfInter890 J X :=
  Subgroup.isPerfect_iff.mp
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect (J ⊓ X))

theorem r890_odd_three_le_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz X n) :
    Odd n ∧ 3 ≤ n := by
  obtain ⟨-, -, -, -, hodd, h3⟩ := h.admissible
  exact ⟨hodd, h3⟩

theorem r890_commutator_eq_bot_of_perfect {G : Type} [Group G] {K W : Subgroup G}
    (hK : ⁅K, K⁆ = K)
    (hW : ⁅W, K⁆ ≤ centralizer (K : Set G)) : ⁅W, K⁆ = ⊥ := by
  have h1 : ⁅⁅W, K⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hW
  have h2 : ⁅⁅K, W⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm K W]; exact h1
  have h3 : ⁅⁅K, K⁆, W⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hK, Subgroup.commutator_comm] at h3
  exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
