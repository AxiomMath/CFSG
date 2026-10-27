module

public import CFSG.RankThree.PartOne.S13K.KF133One

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

structure Row8Conf (p g : ℕ) (Q : Type) [Group Q] (Ē : Subgroup Q) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  g_two : 2 ≤ g
  p_dvd : p ∣ 2 ^ g + 1
  quasisimple : CFSG.IsQuasisimple Q
  center_p : IsPGroup p (Subgroup.center Q)
  onList : Census3.TheoremThreeList (Q ⧸ Subgroup.center Q)
  elem : IsElementaryAbelian p Ē
  card : Nat.card Ē = p ^ 2
  max : ∀ F : Subgroup Q, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (Ē : Set Q) →
    Ē ≤ F → F ≤ Ē ⊔ Subgroup.center Q
  conf : ∃ c ∈ Ē, c ≠ 1 ∧ ∃ (Kb : Subgroup Q) (x : Q),
    Kb ≤ Subgroup.centralizer ({c} : Set Q) ∧
    (Kb.subgroupOf (Subgroup.centralizer ({c} : Set Q))).Normal ∧
    StatedClassicalModel Kb .PSL 2 2 g ∧ x ∈ Kb ∧ orderOf x = p ∧
    Ē = Subgroup.zpowers c ⊔ Subgroup.zpowers x

@[expose] def Row8U3Concl (g : ℕ) (Q : Type) [Group Q] (Ē : Subgroup Q) : Prop :=
  Subgroup.center Q = ⊥ ∧ (Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) →
    StatedClassicalModel Q .PSU 3 2 g)

@[expose] def Row8U3At (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (p g : ℕ) (Ē : Subgroup Q),
    P (Q ⧸ Subgroup.center Q) → Row8Conf p g Q Ē → Row8U3Concl g Q Ē

theorem Row8U3At.of_exists {ι : Type} {P : (X : Type) → [Group X] → Prop}
    {Q : ι → (X : Type) → [Group X] → Prop} (hcov : ∀ (X : Type) [Group X], P X → ∃ i, Q i X)
    (h : ∀ i, Row8U3At (Q i)) : Row8U3At P := fun T _ _ p g Ē hP hc => by
  obtain ⟨i, hi⟩ := hcov _ hP
  exact h i T p g Ē hi hc

@[expose] def Row8U3Inspection : Prop := Row8U3At fun _ _ => True

@[expose] def Row8U3Item (i : Fin 9) : Prop := Row8U3At (thmThreeItem i)

theorem row8U3_of_items (h : ∀ i : Fin 9, Row8U3Item i) : Row8U3Inspection := by
  intro T _ _ p g Ē _ hc
  have hl := hc.onList
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact h 0 T p g Ē h1 hc
  · exact h 1 T p g Ē h2 hc
  · exact h 2 T p g Ē h3 hc
  · exact h 3 T p g Ē h4 hc
  · exact h 4 T p g Ē h5 hc
  · exact h 5 T p g Ē h6 hc
  · exact h 6 T p g Ē h7 hc
  · exact h 7 T p g Ē h8 hc
  · exact h 8 T p g Ē h9 hc

end CFSG.RankThree.PartOne.Q1327T
