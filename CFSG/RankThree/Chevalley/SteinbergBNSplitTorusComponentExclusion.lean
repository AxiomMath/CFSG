module

public import CFSG.RankThree.Chevalley.SteinbergCFHigherExceptionalCrossQuadratic
public import CFSG.RankThree.CentralCover.SteinbergBNF4SplitTorus
public import CFSG.RankThree.CentralCover.SteinbergBNOrdinaryESplitTorus

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem four_le_localRank_of_split_torus {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hpq : p ∣ Nat.card K - 1)
    (e : L ⧸ Subgroup.center L ≃* AdjointQuotient τ K) : 4 ≤ localRank p L := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_adjointGroup e
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rwa [Nat.card_units])
  have hpq' : p ∣ Fintype.card K - 1 := by rwa [← Nat.card_eq_fintype_card]
  rcases hτ with rfl | hτ
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
      CFSG.RankThree.CentralCover.F4_split_torus_actual_central_cover_two_local_rank
        (⊤ : Subgroup L) hp (by omega) hpq' φ hφ hker hζ
    exact h
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
      CFSG.RankThree.CentralCover.ordinary_E_split_torus_actual_central_cover_two_local_rank
        (⊤ : Subgroup L) τ hτ hp hp3 hpq' φ hφ hker hζ
    have : 6 ≤ τ.rank := by rcases hτ with rfl | rfl | rfl <;> decide
    omega

theorem F4_cross_prime_actual_component_toral_factor_restriction {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal] (hN : ¬p ∣ Nat.card N)
    (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .F4 ℓ f) :
    ¬p ∣ ℓ ^ f - 1 ∧ (ℓ ≠ 2 → ¬p ∣ ℓ ^ f + 1 ∧ ¬p ∣ (ℓ ^ f) ^ 2 - 1) := by
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  refine ⟨fun hpq => ?_, fun hℓ2 => ?_⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
    have := four_le_localRank_of_split_torus hp hp3 (Or.inl rfl) (by rw [hK]; exact hpq) e
    omega
  · have key : ¬p ∣ (ℓ ^ f) ^ 2 - 1 := fun hpq =>
      odd_higher_ordinary_exceptional_cross_prime_quadratic_factor_exclusion hp hp3 N hN hX L hℓ
        hℓ2 hpq (Or.inl rfl) hmod
    have hfac : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have := Nat.sq_sub_sq (ℓ ^ f) 1
      rwa [one_pow] at this
    exact ⟨fun h => key (hfac ▸ Dvd.dvd.mul_right h _), key⟩

theorem even_ordinary_E_split_prime_actual_component_exclusion {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal] (hN : ¬p ∣ Nat.card N)
    (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {τ : StatedLieTag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) τ 2 f) : ¬p ∣ 2 ^ f - 1 := by
  intro hpq
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  have key : ∀ τ' : Tag, (τ' = .E6 ∨ τ' = .E7 ∨ τ' = .E8) →
      UntwistedChevalleyModel (L ⧸ Subgroup.center L) τ' (2 ^ f) → False := by
    rintro τ' hτ' ⟨K, _, _, hK, ⟨e⟩⟩
    have := four_le_localRank_of_split_torus hp hp3 (Or.inr hτ') (by rw [hK]; exact hpq) e
    omega
  rcases hτ with rfl | rfl | rfl
  · exact key .E6 (Or.inl rfl) hmod.2
  · exact key .E7 (Or.inr (Or.inl rfl)) hmod.2
  · exact key .E8 (Or.inr (Or.inr rfl)) hmod.2

end CFSG.RankThree.Chevalley
