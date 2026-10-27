module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {Y : Type} [Group Y]

structure E68Hyp (L A R : Subgroup Y) (z : Y) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥L
  elemAbelian : IsElemAbelian 2 A
  mem : z ∈ A
  isPGroup : IsPGroup 2 R
  le : A ≤ R
  centralizer : R ≤ Subgroup.centralizer (A : Set Y)
  normalizer : R ≤ Subgroup.normalizer (L : Set Y)
  sylow : IsSylowTwoOf (R ⊓ L) L
  four_le : 4 ≤ (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A
  centralizes : ∀ a ∈ A, a ∉ Subgroup.centralizer (L : Set Y) → ∀ y ∈ L, y * a = a * y →
    (∃ k : ℕ, y ^ 2 ^ k = 1) → y ∈ Subgroup.centralizer (A : Set Y)

@[expose] def E68Concl (L A R : Subgroup Y) : Prop :=
  ∃ x ∈ L, Odd (orderOf x) ∧ (∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ R) ∧
    ((∀ a ∈ A, ∃ b ∈ A, x * a * x⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set Y)) →
      ∀ j : ℕ, ((∀ a ∈ A, x ^ j * a * (x ^ j)⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set Y)) ↔
        ((A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A - 1) ∣ j))

@[expose] def E68ComponentFactsLie : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y) (z : Y),
    Lemma115CaseA L z → E68Hyp L A R z → E68Concl L A R

@[expose] def E68ComponentFactsCover : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y) (z : Y),
    Lemma115CaseB L z → E68Hyp L A R z → E68Concl L A R

@[expose] def E68ComponentFactsAlt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y) (z : Y),
    (Lemma115CaseC L z ∨ Lemma115CaseD L z) → E68Hyp L A R z → E68Concl L A R

@[expose] def E68ComponentFactsL2p : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y) (z : Y),
    Lemma115CaseE L z → E68Hyp L A R z → E68Concl L A R

@[expose] def E68ComponentFactsSpor : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y) (z : Y),
    Lemma115CaseF L z → E68Hyp L A R z → E68Concl L A R

@[expose] def E68ComponentFacts : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y) (z : Y),
    Lemma115Cases L z → E68Hyp L A R z → E68Concl L A R

theorem e68ComponentFacts_of_cases (hA : E68ComponentFactsLie) (hB : E68ComponentFactsCover)
    (hCD : E68ComponentFactsAlt) (hE : E68ComponentFactsL2p) (hF : E68ComponentFactsSpor) :
    E68ComponentFacts := by
  intro Y _ _ L A R z hc h
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact hA Y L A R z hc h
  · exact hB Y L A R z hc h
  · exact hCD Y L A R z (Or.inl hc) h
  · exact hCD Y L A R z (Or.inr hc) h
  · exact hE Y L A R z hc h
  · exact hF Y L A R z hc h

end E6
end CFSG.Quasithin
