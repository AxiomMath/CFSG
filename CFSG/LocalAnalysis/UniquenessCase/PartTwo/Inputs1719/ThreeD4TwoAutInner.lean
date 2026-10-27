module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Chevalley.GraphTwistedOuterTwoPart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Is3D4)

@[expose] def K_3D4TwoAutInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Is3D4 X n → Odd n →
    ∀ α : X ≃* X, (∃ e : ℕ, α ^ (2 ^ e) = 1) → ∃ g : X, ∀ x : X, α x = g * x * g⁻¹

theorem k_3D4TwoAutInner_holds :
    K_3D4TwoAutInner := by
  intro X _ _ n hX hn α ⟨e, he⟩
  have hX' : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX).2
  obtain ⟨-, h2, -⟩ := CFSG.LieType.Chevalley.graph_twisted_exceptional_model_outer_two_part_bound
    X .trialityD4 2 n 3 hX' (Or.inr ⟨rfl, rfl⟩)
  have hord := (h2 rfl).trans (CFSG.LieType.Chevalley.ordProj_two_of_odd hn)
  have : Finite (MulAut X) := MulEquiv.finite_left
  have hpos : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≠ 0 :=
    Nat.card_pos.ne'
  have hfac : (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)).factorization
      2 = 0 := by
    rcases Nat.pow_eq_one.mp hord with h | h
    · omega
    · exact h
  have hodd : ¬ 2 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
    intro h
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos).mp h
    omega
  set a : CFSG.ComponentClassification.OuterAutomorphisms.Outer X := QuotientGroup.mk α
  have ha1 : a ^ 2 ^ e = 1 := by rw [← QuotientGroup.mk_pow, he, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ e)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have h1 : orderOf a = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha1) (orderOf_dvd_natCard a)
  have hmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
    (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, fun x => by rw [← hg]; exact MulAut.conj_apply g x⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
