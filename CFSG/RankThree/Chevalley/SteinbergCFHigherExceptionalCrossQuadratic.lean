module

public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFOddFourCommutingSL2
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2CrossPrime
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem four_le_localRank_of_higherExceptional_cross {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) (hpq : p ∣ Nat.card K ^ 2 - 1)
    (e : L ⧸ Subgroup.center L ≃* AdjointQuotient τ K) : 4 ≤ localRank p L := by
  have : Fintype K := Fintype.ofFinite K
  have hK2 : ringChar K ≠ 2 := by
    intro h
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card, Nat.odd_iff] at *
    omega
  obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_adjointGroup e
  obtain ⟨ι, hι, hcomm⟩ := higher_ordinary_exceptional_four_commuting_faithful_SL2 K hK2 τ hτ
  obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.commuting_SL2_actual_central_cover_cross_prime_local_rank
      (⊤ : Subgroup L) (by rw [← Nat.card_eq_fintype_card]; exact hK) hp hp2
      (by rw [← Nat.card_eq_fintype_card]; exact hpq) (by norm_num : 1 ≤ 4) φ hφ hker ι hι hcomm
  exact hrank

theorem odd_higher_ordinary_exceptional_cross_prime_quadratic_factor_exclusion {X : Type}
    [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hpq : p ∣ (ℓ ^ f) ^ 2 - 1) {τ : StatedLieTag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ¬ChevalleyExceptionalModel (L ⧸ Subgroup.center L) τ ℓ f := by
  intro hmod
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have key : ∀ τ' : Tag, (τ' = .F4 ∨ τ' = .E6 ∨ τ' = .E7 ∨ τ' = .E8) →
      UntwistedChevalleyModel (L ⧸ Subgroup.center L) τ' (ℓ ^ f) → False := by
    rintro τ' hτ' ⟨K, _, _, hK, ⟨e⟩⟩
    have := four_le_localRank_of_higherExceptional_cross hp (by omega) hτ' (hK ▸ hodd)
      (hK ▸ hpq) e
    omega
  rcases hτ with rfl | rfl | rfl | rfl
  · exact key .F4 (Or.inl rfl) hmod.2
  · exact key .E6 (Or.inr (Or.inl rfl)) hmod.2
  · exact key .E7 (Or.inr (Or.inr (Or.inl rfl))) hmod.2
  · exact key .E8 (Or.inr (Or.inr (Or.inr rfl))) hmod.2

end CFSG.RankThree.Chevalley
