module

public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.KFTransfer

public section

namespace CFSG.RankThree.PartOne.KFCL

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

@[expose] def OutcomeEven (r : ℕ) {G : Type} [Group G] (p : ℕ) (E A I : Subgroup G) : Prop :=
  match r with
  | 1 => Outcome152One p E A I
  | 2 => Outcome152Two p E A I
  | 3 => Outcome152Three p E A I
  | 4 => Outcome152Four p E A I
  | _ => False

section OutcomeEven

variable {G : Type} [Group G] {p : ℕ} {E A I : Subgroup G}

theorem OutcomeEven.outcome152 {r : ℕ} (h : OutcomeEven r p E A I) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    Outcome152 p E A I := by
  interval_cases r
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem OutcomeEven.eq {r : ℕ} (h : OutcomeEven r p E A I) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) : E = A := by
  interval_cases r
  · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
    exact hEA
  · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
    exact hEA
  · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
    exact hEA
  · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
    exact hEA

theorem OutcomeEven.not_five {r : ℕ} (h : OutcomeEven r p E A I) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    ¬ Outcome152Five p E A I := by
  rintro ⟨-, -, -, -, -, -, hne, -⟩
  exact hne (h.eq hr1 hr4)

theorem outcome152_cases (h : Outcome152 p E A I) (h5 : ¬ Outcome152Five p E A I) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 4 ∧ OutcomeEven r p E A I := by
  rcases h with h | h | h | h | h
  · exact ⟨1, le_rfl, by norm_num, h⟩
  · exact ⟨2, by norm_num, by norm_num, h⟩
  · exact ⟨3, by norm_num, by norm_num, h⟩
  · exact ⟨4, by norm_num, le_rfl, h⟩
  · exact absurd h h5

end OutcomeEven

@[expose] def KFAtRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    OutcomeEven r p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, ∃ g : ℕ, KFAt p E g t

@[expose] def KFCompGenRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    OutcomeEven r p E A (lieGenerated p E) →
    ∀ e ∈ E, e ≠ 1 → ∀ Q : Subgroup G,
      Q ≤ lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G) →
      IsComponent (Q.subgroupOf (lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G))) →
      Q ≤ Subgroup.closure {x : G | ∃ t ∈ reflectionSet p E, e ∈ autFixedInG E t ∧
        ∃ K : Subgroup G, IsKt p E t K ∧ x ∈ K}

@[expose] def KFAtEven : Prop := ∀ r : ℕ, 1 ≤ r → r ≤ 4 → KFAtRow r

@[expose] def KFCompGenEven : Prop := ∀ r : ℕ, 1 ≤ r → r ≤ 4 → KFCompGenRow r

theorem kfAtEven_of_rows (h1 : KFAtRow 1) (h2 : KFAtRow 2) (h3 : KFAtRow 3) (h4 : KFAtRow 4) :
    KFAtEven := by
  intro r hr1 hr4
  interval_cases r
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem kfCompGenEven_of_rows (h1 : KFCompGenRow 1) (h2 : KFCompGenRow 2) (h3 : KFCompGenRow 3)
    (h4 : KFCompGenRow 4) : KFCompGenEven := by
  intro r hr1 hr4
  interval_cases r
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end CFSG.RankThree.PartOne.KFCL
