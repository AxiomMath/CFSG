module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Assembly
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.LocalRank (thetaT aschbacherSolvableCore)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

section Hypotheses

variable {G : Type} [Group G]

@[expose] def FFNotWeaklyClosed (b : G) : Prop :=
  ∃ g : G, conjugate (Subgroup.zpowers b) g ≤ Subgroup.centralizer ({b} : Set G) ∧
    conjugate (Subgroup.zpowers b) g ≠ Subgroup.zpowers b

@[expose] def FFSylowCommutatorOdd (b : G) : Prop :=
  ∀ B : Subgroup G,
    (∃ P : Sylow 3 ↥(Subgroup.centralizer ({b} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({b} : Set G))).map
        (Subgroup.centralizer ({b} : Set G)).subtype = B) →
    ∀ a ∈ B, a ≠ 1 →
      Odd (Nat.card ↥⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({a} : Set G)), B⁆)

@[expose] def FFSylowHyperplaneOdd (b : G) : Prop :=
  ∀ B : Subgroup G,
    (∃ P : Sylow 3 ↥(Subgroup.centralizer ({b} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({b} : Set G))).map
        (Subgroup.centralizer ({b} : Set G)).subtype = B) →
    ∀ B₀ : Subgroup G, B₀ ≤ B → B₀.relIndex B = 3 → Odd (Nat.card ↥(thetaT 3 B₀))

end Hypotheses

@[expose] def FinkelsteinFrohardtE3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    KProper InCatalog G → IsCharTwoType G → evenRank G = 3 →
    (∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) →
    ∀ b : G, orderOf b = 3 → ∀ L : Subgroup G,
      L ≤ Subgroup.centralizer ({b} : Set G) →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      CFSG.IsQuasisimple L →
      (StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 1 ∨
        StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 5 2 1 ∨
        StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 1) →
      FFNotWeaklyClosed b → FFSylowCommutatorOdd b → FFSylowHyperplaneOdd b →
        Subgroup.center L = ⊥ ∧
        (StatedClassicalModel L .PSL 4 2 1 →
          StatedClassicalModel G .PSL 6 2 1 ∨ StatedClassicalModel G .POmegaMinus 4 2 1) ∧
        (StatedClassicalModel L .PSL 5 2 1 → StatedClassicalModel G .PSL 7 2 1) ∧
        (StatedClassicalModel L .PSp 3 2 1 →
          StatedClassicalModel G .PSp 4 2 1 ∨ ChevalleyExceptionalModel G .F4 2 1)

theorem FinkelsteinFrohardtE3Statement.not_weaklyClosed_of_not_five
    (hFF : FinkelsteinFrohardtE3Statement) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : evenRank G = 3) (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) (b : G)
    (hb : orderOf b = 3) (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hLN : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLq : CFSG.IsQuasisimple L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 1 ∨
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 5 2 1 ∨
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 1)
    (hB : FFSylowCommutatorOdd b) (hC : FFSylowHyperplaneOdd b)
    (hnot : ¬ (StatedClassicalModel G .PSL 6 2 1 ∨ StatedClassicalModel G .POmegaMinus 4 2 1 ∨
      StatedClassicalModel G .PSL 7 2 1 ∨ StatedClassicalModel G .PSp 4 2 1 ∨
      ChevalleyExceptionalModel G .F4 2 1)) :
    ¬ FFNotWeaklyClosed b := by
  intro ha
  obtain ⟨hZ, h1, h2, h3⟩ := hFF G hnonab hK hchar he hq b hb L hLC hLN hLq hmod ha hB hC
  have hLiso : ∀ (t : Open.StatedLieTag) (n : ℕ),
      StatedClassicalModel (L ⧸ Subgroup.center L) t n 2 1 → StatedClassicalModel L t n 2 1 := by
    intro t n h
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) h
  rcases hmod with h | h | h
  · rcases h1 (hLiso _ _ h) with h' | h'
    · exact hnot (Or.inl h')
    · exact hnot (Or.inr (Or.inl h'))
  · exact hnot (Or.inr (Or.inr (Or.inl (h2 (hLiso _ _ h)))))
  · rcases h3 (hLiso _ _ h) with h' | h'
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inr h'))))

end CFSG.RankThree.PartTwo.Sec21
