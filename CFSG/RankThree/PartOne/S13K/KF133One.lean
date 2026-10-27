module

public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.InputsCT
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.Blueprint CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

abbrev SimpleQuot (p : ℕ) {G : Type} [Group G] (I : Subgroup G) : Type :=
  (↥I ⧸ aschbacherSolvableCore p ↥I) ⧸ Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I)

@[expose] def OddOrderOneOrThree (X : Type) [Group X] : Prop :=
  ∀ x : X, Odd (orderOf x) → orderOf x = 1 ∨ orderOf x = 3

theorem OddOrderOneOrThree.of_card_dvd {X : Type} [Group X] [Finite X] {a : ℕ}
    (h : Nat.card X ∣ 2 ^ a * 3) : OddOrderOneOrThree X := by
  intro x hx
  have h1 : orderOf x ∣ 2 ^ a * 3 := (orderOf_dvd_natCard x).trans h
  have h2 : orderOf x ∣ 3 := by
    have hc : Nat.Coprime (orderOf x) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hx)
    exact hc.dvd_of_dvd_mul_left h1
  rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem OddOrderOneOrThree.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OddOrderOneOrThree X) : OddOrderOneOrThree Y := by
  intro y hy
  have := h (e.symm y) (by rwa [MulEquiv.orderOf_eq])
  rwa [MulEquiv.orderOf_eq] at this

@[expose] def KF133Concl {G : Type} [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) (K I : Subgroup G) : Prop :=
  (
    I = K ⊔ inSubgroup (aschbacherSolvableCore p) I ∨
    (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f ∧
      StatedClassicalModel ↥K .PSL 2 2 f ∧
      I = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
        inSubgroup (aschbacherSolvableCore p) I ∧
      inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G)) ≤ L ∧
      IsSUModelTwo 3 f ↥(inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G)))) ∨
    I ∈ thetaCompZeroStarE p E ∨
    (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ StatedClassicalModel ↥K .PSL 2 2 f ∧
      ((StatedClassicalModel (↥I ⧸ aschbacherSolvableCore p ↥I) .PSU 3 2 f ∧
          Nonempty (torusImage E I ≃* Equiv.Perm (Fin 3))) ∨
        (StatedClassicalModel (↥I ⧸ aschbacherSolvableCore p ↥I) .PSp 2 2 f ∧
          Nonempty (torusImage E I ≃* DihedralGroup 4)) ∨
        (LieModel (↥I ⧸ aschbacherSolvableCore p ↥I) .G2 0 2 f ∧
          Nonempty (torusImage E I ≃* DihedralGroup 6)) ∨
        (LieModel (↥I ⧸ aschbacherSolvableCore p ↥I) .trialityD4 0 2 f ∧
          Nonempty (torusImage E I ≃* DihedralGroup 6)) ∨
        (∃ f' : ℕ, f = 3 * f' ∧ LieModel (↥I ⧸ aschbacherSolvableCore p ↥I) .trialityD4 0 2 f' ∧
          Nonempty (torusImage E I ≃* DihedralGroup 6)) ∨
        (LieModel (↥I ⧸ aschbacherSolvableCore p ↥I) .twistedF4 0 2 f ∧
          Nonempty (torusImage E I ≃* GL (Fin 2) (ZMod 3)))) ∧
      OddOrderOneOrThree ↥(torusImage E I)) ∨
    (p = 5 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 2 ∧
      StatedClassicalModel ↥K .PSL 2 2 2 ∧
      (Nonempty ((↥I ⧸ aschbacherSolvableCore p ↥I) ≃* alternatingGroup (Fin 10)) ∨
        Nonempty ((↥I ⧸ aschbacherSolvableCore p ↥I) ≃* NativeSporadic.Carrier .J2) ∨
        Nonempty ((↥I ⧸ aschbacherSolvableCore p ↥I) ≃* NativeSporadic.Carrier .He) ∨
        Nonempty ((↥I ⧸ aschbacherSolvableCore p ↥I) ≃* NativeSporadic.Carrier .Suz) ∨
        StatedClassicalModel (↥I ⧸ aschbacherSolvableCore p ↥I) .POmegaPlus 4 2 1 ∨
        StatedClassicalModel (↥I ⧸ aschbacherSolvableCore p ↥I) .PSp 4 2 1) ∧
      OddOrderOneOrThree ↥(torusImage E I))) ∧
  ((E = A ∧ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) ∨
    ∃ J ∈ thetaCompZeroStarE p E, sectionTenRel p I J) ∧
  (I ∈ thetaCompStarE p E →
    (∀ B : Subgroup G, B ≤ E ⊓ I → torusInvariant E I B → B = ⊥ ∨ B = E ⊓ I) ∨
    (p = 5 ∧ I ∈ thetaCompZeroStarE p E ∧
      ∃ f : ℕ, 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧ IsSUModelTwo 5 f ↥I))

@[expose] def KF133One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ e ∈ autFixedInG E t, e ≠ 1 → ∀ I ∈ thetaComponentsAt p e, K ≤ I →
      KF133Concl p A c L E K I

@[expose] def thmThreeItem : Fin 9 → (X : Type) → [Group X] → Prop
  | 0, X, _ => Census3.ThmThreeItem1 X
  | 1, X, _ => Census3.ThmThreeItem2 X
  | 2, X, _ => Census3.ThmThreeItem3 X
  | 3, X, _ => Census3.ThmThreeItem4 X
  | 4, X, _ => Census3.ThmThreeItem5 X
  | 5, X, _ => Census3.ThmThreeItem6 X
  | 6, X, _ => Census3.ThmThreeItem7 X
  | 7, X, _ => Census3.ThmThreeItem8 X
  | 8, X, _ => Census3.ThmThreeItem9 X

@[expose] def KF133OneItem (i : Fin 9) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ e ∈ autFixedInG E t, e ≠ 1 → ∀ I ∈ thetaComponentsAt p e, K ≤ I →
      thmThreeItem i (SimpleQuot p I) → KF133Concl p A c L E K I

@[expose] def KF133Thm3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, ∀ K : Subgroup G, IsKt p E t K →
    ∀ e ∈ autFixedInG E t, e ≠ 1 → ∀ I ∈ thetaComponentsAt p e, K ≤ I →
      Census3.TheoremThreeList (SimpleQuot p I)

@[expose] def KF133Theta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ e ∈ autFixedInG E t, e ≠ 1 →
      K ≤ Subgroup.centralizer
        (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) : Set G)

@[expose] def KF133Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ e ∈ autFixedInG E t, e ≠ 1 → ∀ I ∈ thetaComponentsAt p e, K ≤ I →
      ((E = A ∧ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
          StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) ∨
        ∃ J ∈ thetaCompZeroStarE p E, sectionTenRel p I J)

theorem KF133One.two (h : KF133One) : KF133Two := by
  intro G _ _ p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI
  exact (h G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI).2.1

theorem kf133One_of_items (hThm3 : KF133Thm3) (h : ∀ i : Fin 9, KF133OneItem i) : KF133One := by
  intro G _ _ p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI
  have hl := hThm3 G p A c L E hH hF hF13 hT t ht K hK e he he1 I hI hKI
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact h 0 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h1
  · exact h 1 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h2
  · exact h 2 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h3
  · exact h 3 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h4
  · exact h 4 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h5
  · exact h 5 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h6
  · exact h 6 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h7
  · exact h 7 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h8
  · exact h 8 G p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI h9

end CFSG.RankThree.PartOne.S13K
