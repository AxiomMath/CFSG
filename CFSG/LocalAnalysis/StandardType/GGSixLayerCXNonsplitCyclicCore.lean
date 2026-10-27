module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcLabel
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Basic
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourNonregular
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint

namespace ExcNonsplit

section Top

variable {C : Type} [Group C]

theorem isComponentOf_top_of_isQuasisimple (hQ : CFSG.IsQuasisimple C) :
    IsComponentOf (⊤ : Subgroup C) ⊤ :=
  ⟨le_rfl, IsSubnormal.refl _, (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ)⟩

theorem eq_top_of_isComponentOf_top [Finite C] (hQ : CFSG.IsQuasisimple C) {X : Subgroup C}
    (hX : IsComponentOf X ⊤) : X = ⊤ := by
  have hQt : CFSG.IsQuasisimple ↥(⊤ : Subgroup C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ
  have hc' : ⁅(⊤ : Subgroup C), ⊤⁆ = ⊤ :=
    CFSG.RankThree.Chevalley.commutator_eq_self_of_isPerfect hQt.1
  have hQ' : CFSG.IsQuasisimple ↥(⁅(⊤ : Subgroup C), ⊤⁆ : Subgroup C) := by
    rw [hc']
    exact hQt
  rw [F4Nonsplit.eq_commutator_of_isComponentOf hQ' hX, hc']

end Top

section Cyclic

variable {C : Type} [Group C]

theorem centralizer_one_eq_top : Subgroup.centralizer ({1} : Set C) = ⊤ :=
  Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (one_mem _))

theorem centralizer_eq_of_mem_zpowers [Finite C] {p : ℕ} (hp : p.Prime) {a b : C}
    (ha : orderOf a = p) (hb : b ∈ Subgroup.zpowers a) (hb1 : b ≠ 1) :
    Subgroup.centralizer ({b} : Set C) = Subgroup.centralizer ({a} : Set C) := by
  have : Fact p.Prime := ⟨hp⟩
  have hbo : orderOf b = p := by
    have h1 : orderOf b ∣ p := ha ▸ orderOf_dvd_of_mem_zpowers hb
    exact ((Nat.dvd_prime hp).1 h1).resolve_left fun h => hb1 (orderOf_eq_one_iff.1 h)
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers a := (Subgroup.zpowers_le).2 hb
  have hcard : Nat.card (Subgroup.zpowers a) ≤ Nat.card (Subgroup.zpowers b) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, ha, hbo]
  have heq : Subgroup.zpowers b = Subgroup.zpowers a := Subgroup.eq_of_le_of_card_ge hle hcard
  have hcb : Subgroup.centralizer ({b} : Set C) = Subgroup.centralizer (Subgroup.zpowers b : Set C) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hca : Subgroup.centralizer ({a} : Set C) = Subgroup.centralizer (Subgroup.zpowers a : Set C) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcb, hca, heq]

variable [Finite C]


theorem ggNonsplitCoreAt_of_cyclic_components {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hQ : CFSG.IsQuasisimple C) (hpC : p ∣ Nat.card C)
    (hcyc : ∀ a b : C, a ^ p = 1 → b ^ p = 1 → a * b = b * a → a ≠ 1 → b ∈ Subgroup.zpowers a)
    (htop : ∀ X : Subgroup C, IsComponentOf X ⊤ →
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
        MarkedModel lab (↥X ⧸ Subgroup.center ↥X) →
          ¬ LargeEvenHalfSplit p lab (Subgroup.center ↥X = ⊥))
    (hcomp : ∀ a : C, orderOf a = p → ∀ X : Subgroup C,
      IsComponentOf X (Subgroup.centralizer {a}) → ¬ p ∣ Nat.card X →
        ¬ GGNbrClauseFiveMarking p a X) :
    GGNonsplitCoreAt C p := by
  have : Fact p.Prime := ⟨hp⟩
  intro a b ha hb hab X hX hpX
  by_cases ha1 : a = 1
  · subst ha1
    rw [centralizer_one_eq_top] at hX
    exact absurd (by rw [eq_top_of_isComponentOf_top hQ hX, Subgroup.card_top]; exact hpC) hpX
  · have hao : orderOf a = p := orderOf_eq_prime ha ha1
    by_cases hb1 : b = 1
    · subst hb1
      rw [centralizer_one_eq_top]
      refine ⟨⊤, isComponentOf_top_of_isQuasisimple hQ, le_top, ?_⟩
      exact ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3
        ⟨a, Subgroup.mem_top _, fun l _ => rfl⟩
        (htop ⊤ (isComponentOf_top_of_isQuasisimple hQ))
        (fun lab hl _ _ => ggRawInnFieldInput_holds p hp hp2 lab hl)
    · have hbz : b ∈ Subgroup.zpowers a := hcyc a b ha hb hab ha1
      rw [centralizer_eq_of_mem_zpowers hp hao hbz hb1]
      exact ⟨X, hX, le_rfl, hcomp a hao X hX hpX⟩

end Cyclic

end ExcNonsplit

end CFSG.StandardType
