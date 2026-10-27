module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace F07

@[expose] def R77E4 (D : Data G) : Prop :=
  D.sig ⊆ D.sig1 → ∀ p ∈ D.sig, p ≠ 2 → CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig →
      ∀ X : Subgroup G, X ≤ D.M → IsPGroup r X → ¬ IsCyclic X → (∀ x ∈ X, x ^ r = 1) →
        ⁅⁅X, X⁆, X⁆ = ⊥ → 3 < CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) →
          rankThreeGamma 1 r X ≤ D.M

theorem R77E4_of_R77 (D : Data G) (h : R77 D) : R77E4 D := by
  intro _ p hp hp2 hsp r hr hr2 hrσ X hXM hXp hnc hexp hcl h3
  exact h p (D.sig_prime p hp).1 hp2 hsp r hr hr2 hrσ X hXM hXp hnc hexp hcl (by omega)
    (Or.inr (Or.inr (Or.inl h3)))

end F07

namespace F08

@[expose] def R869M (D : Data G) : Prop :=
  ∀ L : Subgroup G,
    (L ∈ calC D.M ∨ (L ≤ D.M ∧ D.M ≤ normalizer (L : Set G) ∧ IsProdOfCalC D.M L)) →
    ¬ Thin8 L → UniqueMax D.M L

theorem R869M_of_R869 (D : Data G) (h : R869 D) : R869M D := by
  intro L hL hnt
  have hLM : L ≤ D.M := by
    rcases hL with hL | ⟨hL, -, -⟩
    · exact CFSG.Quasithin.A3.subnormal_le hL.1
    · exact hL
  exact uc22p22u_uniqueMax_of_calN D hLM
    (h L hL L le_rfl (sup_eq_left.2 (Subgroup.map_subtype_le _)) hnt)

end F08

end CFSG.LocalAnalysis.UniquenessCase.UC22
