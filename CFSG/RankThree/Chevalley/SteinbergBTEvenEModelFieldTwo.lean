module

public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.RankThree.Chevalley.OddRankOneExceptionalModel
public import CFSG.RankThree.CentralCover.SteinbergBNEvenCommutingSL2SplitPrime
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem four_le_twoLocalOddRank_of_even_commuting_SL2 {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {H : Type*} [Group H] {k : Type*} [Field k] [Fintype k] {f : ℕ}
    (hf : 2 ≤ f) (hk : Fintype.card k = 2 ^ f) (φ : Y →* H) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (ι : Fin 4 → SL2 k →* H) (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, ι i A * ι j B = ι j B * ι i A) :
    4 ≤ CFSG.twoLocalOddRank X := by
  obtain ⟨r, hr, hr2, hrq⟩ := exists_odd_prime_dvd_two_pow_sub_one hf
  have hkchar : ringChar k = 2 := by
    refine (FiniteField.even_card_iff_char_two (F := k)).2 ?_
    rw [hk, Nat.pow_mod]
    simp [Nat.zero_pow (by omega : 0 < f)]
  obtain ⟨-, -, -, -, A, -, -, hAcard, hrank⟩ :=
    CFSG.RankThree.CentralCover.even_commuting_SL2_actual_central_cover_split_prime_local_rank Y
      hkchar hr hr2 (by rw [hk]; exact hrq) (by norm_num : 1 ≤ 4) φ hφ hker ι hι hcomm
  have hrX : r ∣ Nat.card X :=
    (Dvd.intro_left _ (hAcard.symm.trans (by ring))).trans (Subgroup.card_subgroup_dvd_card A)
  exact hrank.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hr hr2 hrX)

theorem actual_central_cover_even_E_model_field_two {X : Type} [Group X] [Finite X]
    (he : CFSG.twoLocalOddRank X ≤ 3) (Y : Subgroup X) {f : ℕ} (hf : 1 ≤ f) {τ : StatedLieTag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6)
    (hmod : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) τ 2 f) : f = 1 := by
  by_contra hf1
  have hf2 : 2 ≤ f := by omega
  have key : 4 ≤ CFSG.twoLocalOddRank X := by
    have hun : ∀ t : Tag, (t = .E6 ∨ t = .E7 ∨ t = .E8) →
        UntwistedChevalleyModel (Y ⧸ Subgroup.center Y) t (2 ^ f) →
          4 ≤ CFSG.twoLocalOddRank X := by
      intro t ht hm
      obtain ⟨K, _, _, hK, φ, hφ, hker⟩ := exists_surj_adjointGroup_of_model hm
      have : CharP K 2 := by
        have := ringChar_eq_of_card Nat.prime_two hf hK
        exact ringChar.of_eq this
      obtain ⟨ι, hι, hcomm⟩ := even_higher_ordinary_exceptional_four_commuting_faithful_SL2 K t
        (by rcases ht with rfl | rfl | rfl <;> simp)
      have : Fintype K := Fintype.ofFinite K
      exact four_le_twoLocalOddRank_of_even_commuting_SL2 Y hf2
        (by rw [Fintype.card_eq_nat_card, hK]) φ hφ hker.le ι hι hcomm
    rcases hτ with rfl | rfl | rfl | rfl
    · exact hun .E6 (Or.inl rfl) hmod.2
    · exact hun .E7 (Or.inr (Or.inl rfl)) hmod.2
    · exact hun .E8 (Or.inr (Or.inr rfl)) hmod.2
    · obtain ⟨K, _, _, hK, σ, hσ, φ, hφ, hker⟩ :=
        exists_surj_graphFixedRootGroup_of_model Nat.prime_two hf hmod.2
      have : CharP K 2 := by
        have := ringChar_eq_of_card Nat.prime_two (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])
        exact ringChar.of_eq this
      obtain ⟨ι, hι, hcomm⟩ := even_twisted_E6_four_commuting_faithful_fixed_SL2 K σ
      have : Fintype (RingHom.eqLocusField σ (RingHom.id K)) := Fintype.ofFinite _
      exact four_le_twoLocalOddRank_of_even_commuting_SL2 Y hf2
        (by rw [Fintype.card_eq_nat_card]; exact card_eqLocusField_of_pow Nat.prime_two hf hK hσ)
        φ hφ hker.le ι hι hcomm
  omega

end CFSG.RankThree.Chevalley
