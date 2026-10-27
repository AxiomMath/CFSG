module

public import CFSG.RankThree.PartTwo.Setup
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank

variable {G : Type*} [Group G]

@[expose] def lThreeV (E U : Subgroup G) (c : G) : Subgroup G :=
  ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ((U : Set G) ∪ {c})),
    E ⊓ Subgroup.centralizer (U : Set G)⁆

@[expose] def lThreeStarPairs (A E U : Subgroup G) : Set (G × Subgroup G) :=
  {p | p.1 ∈ E ⊓ Subgroup.centralizer (U : Set G) ∧ p.1 ≠ 1 ∧ p.2 ∈ lZeroStarAt A p.1 ∧
    U ≤ Subgroup.normalizer (p.2 : Set G) ∧
    lThreeV E U p.1 ≤ Subgroup.normalizer (p.2 : Set G) ∧
    ⁅p.2, U⁆ = p.2 ∧ ⁅p.2, lThreeV E U p.1⁆ = p.2}

@[expose] def lThreeStar (A : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ lZeroStar A ∧ ∃ E ∈ collectionIn (partTwoE G) A, ∃ U ∈ fourGroups E,
    ∃ c : G, (c, L) ∈ lThreeStarPairs A E U}

@[expose] def lThreeStarAt (A : Subgroup G) (b : G) : Set (Subgroup G) :=
  lThreeStar A ∩ thetaComponentsAt 3 b

theorem mem_lThreeStarPairs_iff {A E U L : Subgroup G} {c : G} :
    (c, L) ∈ lThreeStarPairs A E U ↔
      c ∈ E ⊓ Subgroup.centralizer (U : Set G) ∧ c ≠ 1 ∧ L ∈ lZeroStarAt A c ∧
        U ≤ Subgroup.normalizer (L : Set G) ∧ lThreeV E U c ≤ Subgroup.normalizer (L : Set G) ∧
        ⁅L, U⁆ = L ∧ ⁅L, lThreeV E U c⁆ = L :=
  Iff.rfl

theorem mem_lThreeStar_iff {A L : Subgroup G} :
    L ∈ lThreeStar A ↔ L ∈ lZeroStar A ∧ ∃ E ∈ collectionIn (partTwoE G) A,
      ∃ U ∈ fourGroups E, ∃ c : G, (c, L) ∈ lThreeStarPairs A E U :=
  Iff.rfl

theorem mem_lZeroStar_of_mem_lThreeStarPairs {A E U L : Subgroup G} {c : G}
    (h : (c, L) ∈ lThreeStarPairs A E U) : L ∈ lZeroStar A :=
  lZeroStarAt_subset_lZeroStar A c h.2.2.1

theorem lThreeStar_subset_lZeroStar (A : Subgroup G) : lThreeStar A ⊆ lZeroStar A :=
  fun _ hL => hL.1

theorem lThreeStarAt_subset (A : Subgroup G) (b : G) : lThreeStarAt A b ⊆ lThreeStar A :=
  Set.inter_subset_left

@[expose] def wStar (A : Subgroup G) : Subgroup (MulAut A) :=
  A.normalizerMonoidHom.range

@[expose] def starOf (A X : Subgroup G) : Subgroup (MulAut A) :=
  (X.subgroupOf (Subgroup.normalizer (A : Set G))).map A.normalizerMonoidHom

theorem starOf_le_wStar (A X : Subgroup G) : starOf A X ≤ wStar A := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

theorem starOf_mono (A : Subgroup G) {X Y : Subgroup G} (h : X ≤ Y) :
    starOf A X ≤ starOf A Y :=
  Subgroup.map_mono fun _ hx => h hx

section Linear

variable {P : Type*} [Group P]

@[expose] def commOf (φ : MulAut P) : Subgroup P :=
  Subgroup.closure (Set.range fun a : P => a⁻¹ * φ a)

@[expose] def IsTransvectionOn (φ : MulAut P) : Prop :=
  Nat.card (commOf φ) = 3 ∧ commOf φ ≤ fixedSubgroupOf φ

@[expose] def IsReflectionOn (φ : MulAut P) : Prop :=
  orderOf φ = 2 ∧ Nat.card (commOf φ) = 3

@[expose] def IsIrreducibleOn (S : Subgroup (MulAut P)) : Prop :=
  ∀ B : Subgroup P, (∀ φ ∈ S, B.map φ.toMonoidHom = B) → B = ⊥ ∨ B = ⊤

theorem mem_commOf (φ : MulAut P) (a : P) : a⁻¹ * φ a ∈ commOf φ :=
  Subgroup.subset_closure ⟨a, rfl⟩

theorem commOf_eq_bot_iff (φ : MulAut P) : commOf φ = ⊥ ↔ φ = 1 := by
  constructor
  · intro h
    ext a
    have ha : a⁻¹ * φ a ∈ commOf φ := mem_commOf φ a
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at ha
    exact ha.symm
  · rintro rfl
    rw [commOf, eq_bot_iff, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    simp

end Linear

section Reflections

variable {G : Type} [Group G]

@[expose] def dStar (A : Subgroup G) : Set (MulAut A) :=
  {φ | IsReflectionOn φ ∧ ∃ X ∈ lThreeStar A, φ ∈ starOf A X}

@[expose] def fixedInG (A : Subgroup G) (φ : MulAut A) : Subgroup G :=
  (fixedSubgroupOf φ).map A.subtype

@[expose] def kZero (A : Subgroup G) (φ : MulAut A) : Subgroup G :=
  CFSG.GH74.GLS.oPrimeResidualOf 3
    (inSubgroup CFSG.layer (Subgroup.centralizer (fixedInG A φ : Set G)))

open _root_.Classical in
@[expose] noncomputable def kOf (A : Subgroup G) (φ : MulAut A) : Subgroup G :=
  if StatedClassicalModel (kZero A φ) .PSU 3 2 2 then
    Classical.epsilon fun K : Subgroup G =>
      K ≤ kZero A φ ∧ StatedClassicalModel K .PSL 2 2 2 ∧ A ⊓ kZero A φ ≤ K
  else kZero A φ

@[expose] noncomputable def iGroup (A : Subgroup G) : Subgroup G :=
  ⨆ φ ∈ dStar A, kOf A φ

@[expose] noncomputable def nGroup (A : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (iGroup A : Set G)

theorem kOf_eq_kZero {A : Subgroup G} {φ : MulAut A}
    (h : ¬ StatedClassicalModel (kZero A φ) .PSU 3 2 2) : kOf A φ = kZero A φ := by
  simp only [kOf, h, ↓reduceIte]

theorem kOf_spec {A : Subgroup G} {φ : MulAut A}
    (h : StatedClassicalModel (kZero A φ) .PSU 3 2 2)
    (hK : ∃ K : Subgroup G, K ≤ kZero A φ ∧ StatedClassicalModel K .PSL 2 2 2 ∧
      A ⊓ kZero A φ ≤ K) :
    kOf A φ ≤ kZero A φ ∧ StatedClassicalModel (kOf A φ) .PSL 2 2 2 ∧
      A ⊓ kZero A φ ≤ kOf A φ := by
  have e : kOf A φ = Classical.epsilon fun K : Subgroup G =>
      K ≤ kZero A φ ∧ StatedClassicalModel K .PSL 2 2 2 ∧ A ⊓ kZero A φ ≤ K := by
    simp only [kOf, h, ↓reduceIte]
  rw [e]
  exact Classical.epsilon_spec hK

theorem kOf_le_iGroup {A : Subgroup G} {φ : MulAut A} (hφ : φ ∈ dStar A) :
    kOf A φ ≤ iGroup A :=
  le_iSup₂_of_le φ hφ le_rfl

theorem iGroup_le_nGroup (A : Subgroup G) : iGroup A ≤ nGroup A :=
  Subgroup.le_normalizer

end Reflections

structure Sec21Std (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop where
  standing : PartTwoStanding G
  mem_S : A ∈ partTwoS G
  side : A ∈ partTwoE G → partTwoE G = partTwoF G

structure Sec21Pair (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G)
    (L : Subgroup G) : Prop extends Sec21Std G A where
  mem_E : E ∈ collectionIn (partTwoE G) A
  mem_U : U ∈ fourGroups E
  mem_pair : (c, L) ∈ lThreeStarPairs A E U

end CFSG.RankThree.PartTwo.Sec21
