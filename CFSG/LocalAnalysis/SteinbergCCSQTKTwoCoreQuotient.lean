module

public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis

open Subgroup

namespace SQTKTwoCoreQuotient

theorem isKGroup_quotient {X : Type} [Group X] (hX : IsKGroup X) (M : Subgroup X) [M.Normal] :
    IsKGroup (X ⧸ M) :=
  hX.quotient M

theorem not_dvd_card_pCore_two {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (pCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := H))
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

end SQTKTwoCoreQuotient

open SQTKTwoCoreQuotient in
theorem SQTK_two_core_quotient {H : Type} [Group H] [Finite H] (hH : IsSQTK H) :
    IsSQTK (H ⧸ pCore 2 H) ∧ pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
  obtain ⟨hsqt, hK⟩ := hH
  refine ⟨⟨fun p hp hp2 => ?_, isKGroup_quotient hK _⟩, ABGLocalTools.pCore_quotient_pCore_eq_bot⟩
  rw [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _
    (not_dvd_card_pCore_two hp hp2)]
  exact hsqt p hp hp2

end CFSG.LocalAnalysis
