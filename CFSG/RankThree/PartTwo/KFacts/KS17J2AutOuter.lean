module

public import CFSG.RankThree.PartTwo.KFacts.KS17J2Aut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ComponentClassification.OuterAutomorphisms

theorem ks17J2AutThree_of_outer
    (h : Nonempty (Outer CFSG.Blueprint.NativeSporadic.J2 ≃* Multiplicative (ZMod 2))) :
    KS17J2AutThree := by
  intro X _ hX σ hσ
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ := h
  set φ : Outer X ≃* Multiplicative (ZMod 2) := (equivalence e).trans f
  have hsq : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h1 : φ (σ : Outer X) = 1 := by
    have h3 : φ (σ : Outer X) ^ 3 = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one, map_one]
    have h32 : φ (σ : Outer X) ^ 3 = φ (σ : Outer X) ^ 2 * φ (σ : Outer X) := pow_succ _ 2
    rw [hsq, one_mul, h3] at h32
    exact h32.symm
  have h2 : (σ : Outer X) = 1 := φ.injective (h1.trans (map_one φ).symm)
  have h4 : σ ∈ inner X := (QuotientGroup.eq_one_iff σ).mp h2
  exact h4

end CFSG.RankThree.PartTwo.KFacts
