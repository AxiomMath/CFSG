module

public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFTwistedE6CommutingSL2
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2CrossPrime
public import CFSG.RankThree.CentralCover.SteinbergBNEvenCommutingSL2SplitPrime
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)

theorem twisted_E6_cross_prime_actual_component_toral_factor_restriction {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .twistedE6 ℓ f) :
    ¬p ∣ ℓ ^ f - 1 ∧ (ℓ ≠ 2 → ¬p ∣ ℓ ^ f + 1 ∧ ¬p ∣ (ℓ ^ f) ^ 2 - 1) := by
  have hQ := CFSG.RankThree.Classical2.localRank_quotient_le hp (by omega) N hN
  have hcontra : ¬4 ≤ localRank p (X ⧸ N) := fun h => by
    have := h.trans (hQ.trans hX)
    omega
  obtain ⟨-, hmodel⟩ := hmod
  obtain ⟨K, _, _, hK, σ, hσ, φ, hφ, hker⟩ := exists_surj_graphFixedRootGroup_of_model hℓ hf hmodel
  have hcharK : ringChar K = ℓ :=
    ringChar_eq_of_card hℓ (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])
  have : Fintype (RingHom.eqLocusField σ (RingHom.id K)) := Fintype.ofFinite _
  have hk : Fintype.card (RingHom.eqLocusField σ (RingHom.id K)) = ℓ ^ f := by
    rw [Fintype.card_eq_nat_card]
    exact card_eqLocusField_of_pow hℓ hf hK hσ
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have : CharP K 2 := ringChar.of_eq hcharK
    obtain ⟨ι, hι, hcomm⟩ := even_twisted_E6_four_commuting_faithful_fixed_SL2 K σ
    have hkchar : ringChar (RingHom.eqLocusField σ (RingHom.id K)) = 2 := by
      refine (FiniteField.even_card_iff_char_two
        (F := RingHom.eqLocusField σ (RingHom.id K))).2 ?_
      rw [hk, Nat.pow_mod]
      simp [Nat.zero_pow (by omega : 0 < f)]
    refine ⟨fun hpq => hcontra ?_, fun h => absurd rfl h⟩
    obtain ⟨-, -, -, -, -, -, -, -, hrank⟩ :=
      CFSG.RankThree.CentralCover.even_commuting_SL2_actual_central_cover_split_prime_local_rank
        L hkchar hp (by omega) (by rw [hk]; exact hpq) (by norm_num : 1 ≤ 4) φ hφ hker.le ι hι
        hcomm
    exact hrank
  · have hchar : ringChar K ≠ 2 := by
      rw [hcharK]
      exact hℓ2
    obtain ⟨ι, hι, hcomm⟩ := twisted_E6_four_commuting_faithful_fixed_SL2 K hchar σ
    have hodd : Odd (Fintype.card (RingHom.eqLocusField σ (RingHom.id K))) := by
      rw [hk]
      exact (hℓ.odd_of_ne_two hℓ2).pow
    have key : ¬p ∣ (ℓ ^ f) ^ 2 - 1 := fun hpq => hcontra (by
      obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
        CFSG.RankThree.CentralCover.commuting_SL2_actual_central_cover_cross_prime_local_rank L
          hodd hp (by omega) (by rw [hk]; exact hpq) (by norm_num : 1 ≤ 4) φ hφ hker.le ι hι
          hcomm
      exact hrank)
    have hfac : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have := Nat.sq_sub_sq (ℓ ^ f) 1
      rwa [one_pow] at this
    refine ⟨fun h => key (hfac ▸ Dvd.dvd.mul_left h _), fun _ =>
      ⟨fun h => key (hfac ▸ Dvd.dvd.mul_right h _), key⟩⟩

end CFSG.RankThree.Chevalley
