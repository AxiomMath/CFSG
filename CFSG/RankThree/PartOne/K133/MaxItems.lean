module

public import CFSG.RankThree.PartOne.K133.Max

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K TauCeti
open CFSG.RankThree.PartOne.Census3

@[expose] def KF133ResMaxAt (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ b ∈ autFixedInG E t, b ≠ 1 → ∀ J ∈ thetaComponentsAt p b, K ≤ J →
      J ∈ thetaCompStarE p E → thetaQuotientCentralizer p E J = Subgroup.zpowers b →
      c ∉ Subgroup.zpowers b → P (SimpleQuot p J) →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 3 ∧ J ∈ sectionTenZero p B

theorem KF133ResMaxAt.mono {P Q : (X : Type) → [Group X] → Prop}
    (hPQ : ∀ (X : Type) [Group X], P X → Q X) (h : KF133ResMaxAt Q) : KF133ResMaxAt P :=
  fun G _ _ p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc hP =>
    h G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc (hPQ _ hP)

theorem KF133ResMaxAt.of_exists {ι : Type} {P : (X : Type) → [Group X] → Prop}
    {Q : ι → (X : Type) → [Group X] → Prop} (hcov : ∀ (X : Type) [Group X], P X → ∃ i, Q i X)
    (h : ∀ i, KF133ResMaxAt (Q i)) : KF133ResMaxAt P :=
  fun G _ _ p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc hP => by
    obtain ⟨i, hi⟩ := hcov _ hP
    exact h i G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc hi

@[expose] def KF133ResMaxItem (i : Fin 9) : Prop :=
  KF133ResMaxAt (thmThreeItem i)

theorem kf133ResMax_of_items (hThm3 : KF133Thm3) (h : ∀ i : Fin 9, KF133ResMaxItem i) :
    KF133ResMax := by
  intro G _ _ p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc
  have hl := hThm3 G p A c L E hH hF hF13 hT t ht K hK b hb hb1 J hJ hKJ
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact h 0 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h1
  · exact h 1 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h2
  · exact h 2 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h3
  · exact h 3 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h4
  · exact h 4 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h5
  · exact h 5 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h6
  · exact h 6 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h7
  · exact h 7 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h8
  · exact h 8 G p A c L E hH hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc h9

@[expose] def leaf2 : Fin 2 → (X : Type) → [Group X] → Prop
  | 0, X, _ => ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent ≤ 3 ∧ IsoLie X (.A 2 q)
  | 1, X, _ => ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent ≤ 3 ∧ IsoLie X (.twistedA 2 q)

@[expose] def leaf4 : Fin 4 → (X : Type) → [Group X] → Prop
  | 0, X, _ => ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent = 1 ∧ IsoLie X (.G2 q)
  | 1, X, _ => ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent = 1 ∧ IsoLie X (.B 2 q)
  | 2, X, _ => ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent = 1 ∧ IsoLie X (.twistedA 3 q)
  | 3, X, _ => ∃ q : PrimePower, q.p ≠ 2 ∧ q.exponent = 1 ∧ IsoLie X (.A 3 q)

@[expose] def leaf6 (s : SporadicName) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* (CFSGIndex.sporadic s).Group)

@[expose] def leaf7 : Fin 11 → (X : Type) → [Group X] → Prop
  | 0, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.A 1 q)
  | 1, X, _ => ∃ m : ℕ, IsoLie X (.suzuki m)
  | 2, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.twistedA 2 q)
  | 3, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.A 2 q)
  | 4, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.B 2 q)
  | 5, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.G2 q)
  | 6, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.twistedA 3 q)
  | 7, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.twistedA 4 q)
  | 8, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.trialityD4 q)
  | 9, X, _ => ∃ m : ℕ, IsoLie X (.reeF4 m)
  | 10, X, _ => IsoLie X .tits

@[expose] def leaf8 : Fin 3 → (X : Type) → [Group X] → Prop
  | 0, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.A 3 q)
  | 1, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.B 3 q)
  | 2, X, _ => ∃ q : PrimePower, q.p = 2 ∧ IsoLie X (.twistedD 4 q)

@[expose] def leaf9 : Fin 7 → (X : Type) → [Group X] → Prop
  | 0, X, _ => ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.A 4 q)
  | 1, X, _ => ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.A 5 q)
  | 2, X, _ => ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.A 6 q)
  | 3, X, _ => ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.twistedA 5 q)
  | 4, X, _ => ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.B 4 q)
  | 5, X, _ => ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.D 4 q)
  | 6, X, _ => ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.F4 q)

theorem kf133ResMaxItem_one_of_leaves (h : ∀ i, KF133ResMaxAt (leaf2 i)) : KF133ResMaxItem 1 :=
  KF133ResMaxAt.of_exists (Q := leaf2) (fun X _ hX => by
    obtain ⟨q, hq, he, h | h⟩ := hX
    · exact ⟨0, q, hq, he, h⟩
    · exact ⟨1, q, hq, he, h⟩) h

theorem kf133ResMaxItem_three_of_leaves (h : ∀ i, KF133ResMaxAt (leaf4 i)) : KF133ResMaxItem 3 :=
  KF133ResMaxAt.of_exists (Q := leaf4) (fun X _ hX => by
    obtain ⟨q, hq, he, h0 | h1 | h2 | h3⟩ := hX
    · exact ⟨0, q, hq, he, h0⟩
    · exact ⟨1, q, hq, he, h1⟩
    · exact ⟨2, q, hq, he, h2⟩
    · exact ⟨3, q, hq, he, h3⟩) h

theorem kf133ResMaxItem_five_of_leaves (h : ∀ s ∈ sporadicsThm3, KF133ResMaxAt (leaf6 s)) :
    KF133ResMaxItem 5 :=
  KF133ResMaxAt.of_exists (ι := {s : SporadicName // s ∈ sporadicsThm3})
    (Q := fun s => leaf6 s.1) (fun X _ hX => by
      obtain ⟨s, hs, hX⟩ := hX
      exact ⟨⟨s, hs⟩, hX⟩) (fun s => h s.1 s.2)

theorem kf133ResMaxItem_six_of_leaves (h : ∀ i, KF133ResMaxAt (leaf7 i)) : KF133ResMaxItem 6 :=
  KF133ResMaxAt.of_exists (Q := leaf7) (fun X _ hX => by
    rcases hX with ⟨q, hq, h0⟩ | ⟨m, h1⟩ | ⟨q, hq, h2 | h3 | h4 | h5 | h6 | h7 | h8⟩ | ⟨m, h9⟩ | h10
    · exact ⟨0, q, hq, h0⟩
    · exact ⟨1, m, h1⟩
    · exact ⟨2, q, hq, h2⟩
    · exact ⟨3, q, hq, h3⟩
    · exact ⟨4, q, hq, h4⟩
    · exact ⟨5, q, hq, h5⟩
    · exact ⟨6, q, hq, h6⟩
    · exact ⟨7, q, hq, h7⟩
    · exact ⟨8, q, hq, h8⟩
    · exact ⟨9, m, h9⟩
    · exact ⟨10, h10⟩) h

theorem kf133ResMaxItem_seven_of_leaves (h : ∀ i, KF133ResMaxAt (leaf8 i)) : KF133ResMaxItem 7 :=
  KF133ResMaxAt.of_exists (Q := leaf8) (fun X _ hX => by
    obtain ⟨q, hq, h0 | h1 | h2⟩ := hX
    · exact ⟨0, q, hq, h0⟩
    · exact ⟨1, q, hq, h1⟩
    · exact ⟨2, q, hq, h2⟩) h

theorem kf133ResMaxItem_eight_of_leaves (h : ∀ i, KF133ResMaxAt (leaf9 i)) : KF133ResMaxItem 8 :=
  KF133ResMaxAt.of_exists (Q := leaf9) (fun X _ hX => by
    obtain ⟨q, hq, he, h0 | h1 | h2 | h3 | h4 | h5 | h6⟩ := hX
    · exact ⟨0, q, hq, he, h0⟩
    · exact ⟨1, q, hq, he, h1⟩
    · exact ⟨2, q, hq, he, h2⟩
    · exact ⟨3, q, hq, he, h3⟩
    · exact ⟨4, q, hq, he, h4⟩
    · exact ⟨5, q, hq, he, h5⟩
    · exact ⟨6, q, hq, he, h6⟩) h

theorem kf133ResMax_of_leaves (hThm3 : KF133Thm3) (h1 : KF133ResMaxItem 0)
    (h2 : ∀ i, KF133ResMaxAt (leaf2 i)) (h3 : KF133ResMaxItem 2)
    (h4 : ∀ i, KF133ResMaxAt (leaf4 i)) (h5 : KF133ResMaxItem 4)
    (h6 : ∀ s ∈ sporadicsThm3, KF133ResMaxAt (leaf6 s)) (h7 : ∀ i, KF133ResMaxAt (leaf7 i))
    (h8 : ∀ i, KF133ResMaxAt (leaf8 i)) (h9 : ∀ i, KF133ResMaxAt (leaf9 i)) : KF133ResMax := by
  refine kf133ResMax_of_items hThm3 fun i => ?_
  fin_cases i
  · exact h1
  · exact kf133ResMaxItem_one_of_leaves h2
  · exact h3
  · exact kf133ResMaxItem_three_of_leaves h4
  · exact h5
  · exact kf133ResMaxItem_five_of_leaves h6
  · exact kf133ResMaxItem_six_of_leaves h7
  · exact kf133ResMaxItem_seven_of_leaves h8
  · exact kf133ResMaxItem_eight_of_leaves h9

end CFSG.RankThree.PartOne.K133
