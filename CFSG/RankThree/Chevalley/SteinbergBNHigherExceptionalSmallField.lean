module

public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFOddFourCommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergCFTwistedE6CommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityDefiningComponent
public import CFSG.RankThree.Chevalley.OddRankOneExceptionalModel
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2CrossPrime
public import CFSG.RankThree.CentralCover.SteinbergBNF4SplitTorus
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem exists_odd_prime_dvd_sq_sub_one {q : ℕ} (hq : Odd q) (hq3 : 3 < q) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ q ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ := hq
  have hfac : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    have h : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  obtain ⟨n, hn, hn3, hdvd⟩ : ∃ n, Odd n ∧ 3 ≤ n ∧ n ∣ m * (m + 1) := by
    rcases Nat.even_or_odd m with he | ho
    · exact ⟨m + 1, he.add_one, by omega, dvd_mul_left _ _⟩
    · obtain ⟨k, rfl⟩ := ho
      exact ⟨2 * k + 1, ⟨k, rfl⟩, by omega, dvd_mul_right _ _⟩
  refine ⟨n.minFac, Nat.minFac_prime (by omega), fun h => ?_, ?_⟩
  · have h2 : 2 ∣ n := h ▸ Nat.minFac_dvd n
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr h2)
  · rw [hfac]
    exact (Nat.minFac_dvd n).trans (hdvd.mul_left 4)

theorem four_le_twoLocalOddRank_of_four_le_localRank {X : Type*} [Group X] [Finite X] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (h : 4 ≤ localRank r X) : 4 ≤ CFSG.twoLocalOddRank X :=
  h.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hr hr2
    (CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hr (by omega)))

theorem four_le_twoLocalOddRank_of_odd_commuting_SL2 {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {H : Type*} [Group H] {k : Type*} [Field k] [Fintype k]
    (hk : Odd (Fintype.card k)) (hk3 : 3 < Fintype.card k) (φ : Y →* H)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) (ι : Fin 4 → SL2 k →* H)
    (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, ι i A * ι j B = ι j B * ι i A) :
    4 ≤ CFSG.twoLocalOddRank X := by
  obtain ⟨r, hr, hr2, hrq⟩ := exists_odd_prime_dvd_sq_sub_one hk hk3
  obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.commuting_SL2_actual_central_cover_cross_prime_local_rank Y hk hr
      hr2 hrq (by norm_num : 1 ≤ 4) φ hφ hker ι hι hcomm
  exact four_le_twoLocalOddRank_of_four_le_localRank hr hr2 hrank

theorem three_lt_of_odd_prime_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (h3 : ℓ ^ f ≠ 3) : 3 < ℓ ^ f := by
  have hℓ3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  have : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
  omega

theorem ordinary_higher_exceptional_small_field {X : Type} [Group X] [Finite X]
    (he : CFSG.twoLocalOddRank X ≤ 3) (Y : Subgroup X) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hm : UntwistedChevalleyModel (Y ⧸ Subgroup.center Y) τ (ℓ ^ f)) :
    (ℓ ≠ 2 → ℓ ^ f = 3) ∧ (τ = .F4 → ℓ = 2 → ℓ ^ f = 2) := by
  obtain ⟨K, _, _, hK, φ, hφ, hker⟩ := exists_surj_adjointGroup_of_model hm
  have : Fintype K := Fintype.ofFinite K
  have hcharK : ringChar K = ℓ := ringChar_eq_of_card hℓ hf hK
  have hKcard : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  refine ⟨fun hℓ2 => ?_, fun hτF hℓ2 => ?_⟩
  · by_contra h3
    have hK2 : ringChar K ≠ 2 := by rw [hcharK]; exact hℓ2
    obtain ⟨ι, hι, hcomm⟩ := higher_ordinary_exceptional_four_commuting_faithful_SL2 K hK2 τ hτ
    have := four_le_twoLocalOddRank_of_odd_commuting_SL2 Y
      (by rw [hKcard]; exact (hℓ.odd_of_ne_two hℓ2).pow)
      (by rw [hKcard]; exact three_lt_of_odd_prime_pow hℓ hℓ2 hf h3) φ hφ hker.le ι hι hcomm
    omega
  · subst hτF hℓ2
    by_contra h2
    have hf2 : 2 ≤ f := by
      by_contra hf2
      exact h2 (by rw [show f = 1 by omega, pow_one])
    obtain ⟨r, hr, hr2, hrq⟩ := exists_odd_prime_dvd_two_pow_sub_one hf2
    have : Fact r.Prime := ⟨hr⟩
    have : NeZero r := ⟨hr.ne_zero⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = r :=
      exists_prime_orderOf_dvd_card' r (by rw [Nat.card_units, hK]; exact hrq)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hrank⟩ :=
      CFSG.RankThree.CentralCover.F4_split_torus_actual_central_cover_two_local_rank Y hr hr2
        (by rw [hKcard]; exact hrq) φ hφ hker.le hζ
    have := four_le_twoLocalOddRank_of_four_le_localRank hr hr2 hrank
    omega

theorem twisted_E6_odd_small_field {X : Type} [Group X] [Finite X]
    (he : CFSG.twoLocalOddRank X ≤ 3) (Y : Subgroup X) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hm : TwistedChevalleyModel (Y ⧸ Subgroup.center Y) .E6 (ℓ ^ f)) :
    ℓ ^ f = 3 := by
  by_contra h3
  obtain ⟨K, _, _, hK, σ, hσ, φ, hφ, hker⟩ := exists_surj_graphFixedRootGroup_of_model hℓ hf hm
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card hℓ (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])]
    exact hℓ2
  obtain ⟨ι, hι, hcomm⟩ := twisted_E6_four_commuting_faithful_fixed_SL2 K hchar σ
  have : Fintype (RingHom.eqLocusField σ (RingHom.id K)) := Fintype.ofFinite _
  have hk : Fintype.card (RingHom.eqLocusField σ (RingHom.id K)) = ℓ ^ f := by
    rw [Fintype.card_eq_nat_card]
    exact card_eqLocusField_of_pow hℓ hf hK hσ
  have := four_le_twoLocalOddRank_of_odd_commuting_SL2 Y
    (by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow)
    (by rw [hk]; exact three_lt_of_odd_prime_pow hℓ hℓ2 hf h3) φ hφ hker.le ι hι hcomm
  omega

theorem triality_D4_small_characteristic {X : Type} [Group X] [Finite X]
    (he : CFSG.twoLocalOddRank X ≤ 3) (Y : Subgroup X) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hm : TwistedChevalleyModel (Y ⧸ Subgroup.center Y) .D4 (ℓ ^ f)) : ℓ = 2 ∨ ℓ = 3 := by
  by_contra h23
  have hℓ3 : 3 < ℓ := by
    have := hℓ.two_le
    omega
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  have hY := four_mul_le_localRank_of_triality hℓ hℓ3 hf hK hσ e
  have hYX := CFSG.RankThree.PartTwo.localRank_subgroup_le hℓ Y
  have := four_le_twoLocalOddRank_of_four_le_localRank hℓ (by omega) (by omega : 4 ≤ localRank ℓ X)
  omega

theorem actual_central_cover_higher_exceptional_small_field_restrictions {X : Type} [Group X]
    [Finite X] (he : CFSG.twoLocalOddRank X ≤ 3) (Y : Subgroup X) {ℓ f : ℕ} {τ : StatedLieTag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨ τ = .trialityD4)
    (hmod : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) τ ℓ f) :
    (ℓ ≠ 2 → τ ≠ .trialityD4 → ℓ ^ f = 3) ∧ (τ = .F4 → ℓ = 2 → ℓ ^ f = 2) ∧
      (τ = .trialityD4 → ℓ = 2 ∨ ℓ = 3) ∧ (τ = .F4 → ℓ ^ f = 2 ∨ ℓ ^ f = 3) := by
  have hℓ : ℓ.Prime := hmod.1.1
  have hf : 1 ≤ f := hmod.1.2.1
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hodd, heven⟩ :=
      ordinary_higher_exceptional_small_field he Y hℓ hf (Or.inl rfl) hmod.2
    refine ⟨fun h _ => hodd h, fun _ h => heven rfl h, (fun h => nomatch h), fun _ => ?_⟩
    by_cases hℓ2 : ℓ = 2
    · exact Or.inl (heven rfl hℓ2)
    · exact Or.inr (hodd hℓ2)
  · exact ⟨fun h _ => (ordinary_higher_exceptional_small_field he Y hℓ hf
      (Or.inr (Or.inl rfl)) hmod.2).1 h, (fun h => nomatch h), (fun h => nomatch h),
      (fun h => nomatch h)⟩
  · exact ⟨fun h _ => (ordinary_higher_exceptional_small_field he Y hℓ hf
      (Or.inr (Or.inr (Or.inl rfl))) hmod.2).1 h, (fun h => nomatch h), (fun h => nomatch h),
      (fun h => nomatch h)⟩
  · exact ⟨fun h _ => (ordinary_higher_exceptional_small_field he Y hℓ hf
      (Or.inr (Or.inr (Or.inr rfl))) hmod.2).1 h, (fun h => nomatch h), (fun h => nomatch h),
      (fun h => nomatch h)⟩
  · exact ⟨fun h _ => twisted_E6_odd_small_field he Y hℓ h hf hmod.2, (fun h => nomatch h),
      (fun h => nomatch h), (fun h => nomatch h)⟩
  · exact ⟨fun _ h => absurd rfl h, (fun h => nomatch h),
      fun _ => triality_D4_small_characteristic he Y hℓ hf hmod.2, (fun h => nomatch h)⟩

end CFSG.RankThree.Chevalley
