module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools

public section

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def CatalogHypothesisA (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.Blueprint.Catalog X → Nat.Coprime p (Nat.card X) → signalizerMcBrideHypothesisA p X

@[expose] def PSubgroupsCyclic (p : ℕ) (T : Type*) [Group T] : Prop :=
  ∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P

theorem PSubgroupsCyclic.of_mulEquiv {p : ℕ} {T G : Type*} [Group T] [Group G] (e : T ≃* G)
    (h : PSubgroupsCyclic p G) : PSubgroupsCyclic p T := fun _ hP =>
  CFSG.RankThree.Automorphisms.isCyclic_of_isPGroup_of_mulEquiv e h hP

theorem PSubgroupsCyclic.of_not_dvd_card_mulAut {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (haut : ¬ p ∣ Nat.card (MulAut X)) : PSubgroupsCyclic p X := by
  have : Fact p.Prime := ⟨hp⟩
  intro P hP
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card (MulAut X) := Subgroup.card_subgroup_dvd_card P
  have hk0 : k = 0 := by
    by_contra hne
    exact haut ((dvd_pow_self p hne).trans (hk ▸ hdvd))
  rw [hk0, pow_zero] at hk
  have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
  exact isCyclic_of_subsingleton

theorem not_dvd_card_mulAut_of_not_dvd_outer {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hpX : ¬ p ∣ Nat.card X) (hpO : ¬ p ∣ Nat.card (Outer X)) :
    ¬ p ∣ Nat.card (MulAut X) := by
  intro h
  rw [(inner X).card_eq_card_quotient_mul_card_subgroup] at h
  rcases hp.dvd_mul.mp h with h1 | h1
  · exact hpO h1
  · exact hpX (h1.trans (Subgroup.card_range_dvd _))

theorem hypothesisA_of_not_dvd_card_mulAut {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hcop : Nat.Coprime p (Nat.card X)) (haut : ¬ p ∣ Nat.card (MulAut X)) :
    signalizerMcBrideHypothesisA p X := by
  refine ⟨hp, hsimple, hnonab, hcop, PSubgroupsCyclic.of_not_dvd_card_mulAut hp haut,
    Or.inr fun f hf => ?_⟩
  exact absurd (hf ▸ orderOf_dvd_natCard f) haut

end CFSG.SignalizerFunctorTheorem.CatalogBridge
