module

public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.Quasithin.EmptyFaithful.S152RD4

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.Timmesfeld.ExceptionalOrders


theorem card_dvd_of_sylow_le {X : Type} [Group X] [Finite X]
    (hm : ChevalleyExceptionalModel X .trialityD4 2 1) {U M : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUM : U ≤ M) (hM : M ≠ ⊤) :
    ∃ m : ℕ, Nat.card M ∣ 63 * 2 ^ m := by
  obtain ⟨K, _, _, σ, φ, hK, hσ, hUφ, hres, -⟩ := even_rank_two_residual_triality hm hU
  obtain ⟨M', hM', hMM'⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  obtain ⟨j, hj⟩ := (hres.2.2.1 M' (hUM.trans hMM')).mp hM'.covBy_top
  set a := d4Index j with ha
  have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  have hcardM' : Nat.card M' = Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
    rw [hj, Subgroup.card_map_of_injective φ.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hP := card_graphFixedParabolic_singleton_d4 σ a
  have hB := card_graphFixedRootBorel (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) σ.surjective
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUU : Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) = Nat.card U := by
    have h1 : Nat.card (U.map φ.toMonoidHom) = Nat.card U :=
      Subgroup.card_map_of_injective φ.injective
    rw [hUφ] at h1
    rw [← h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv).symm
  obtain ⟨m, hm2⟩ := IsPGroup.iff_card.mp hU.2.1
  have hLa : ∀ b, Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) =
      (2 ^ 1) ^ (TwistTag.D4.orbit b).card := fun b =>
    card_orbitField_D4_orientation Nat.prime_two le_rfl hK (Or.inl rfl)
      (fun c => by rw [pow_one]; exact hσ c) b
  have hT : Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) ∣ 7 := by
    rw [graphFixedRootTorus_eq_compatTorus σ.surjective]
    have h1 := card_compatTorus_mul (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    rw [card_compatSubgroup, Finset.prod_congr rfl fun b _ => by rw [hLa b]] at h1
    have h2 : ∏ b : Fin TwistTag.D4.foldedTag.rank, ((2 ^ 1) ^ (TwistTag.D4.orbit b).card - 1) =
        7 := by decide
    rw [h2] at h1
    exact Dvd.intro _ h1
  have h9 : 1 + (2 ^ 1) ^ (TwistTag.D4.orbit a).card ∣ 9 := by
    rcases foldedRank_D4_cases a with h | h <;> rw [h] <;> decide
  refine ⟨m, ?_⟩
  have h1 := Subgroup.card_dvd_of_le hMM'
  rw [hcardM', hP, hB, hUU, hm2, hLa a] at h1
  refine h1.trans ?_
  rw [show 63 * 2 ^ m = 7 * 2 ^ m * 9 by ring]
  exact mul_dvd_mul (mul_dvd_mul_right hT _) h9

theorem sylow_sup_sylow_two_eq_top {X : Type} [Group X] [Finite X]
    (hm : ChevalleyExceptionalModel X .trialityD4 2 1) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpX : p ∣ Nat.card X) (R : Sylow p X) (Q : Sylow 2 X) : (R : Subgroup X) ⊔ Q = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card X = 2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 := by
    obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hm
    refine (Nat.card_congr e.toEquiv).trans (((triality_both_orientations_exact_finite_order 2 1
      Nat.prime_two le_rfl K hK 1 (Or.inl rfl) σ.toRingHom fun c => ?_).1).trans (by norm_num))
    rw [pow_one]
    exact hσ c
  by_contra hM
  have hQ : CFSG.QuasithinUnique.IsSylowTwoOf (Q : Subgroup X) ⊤ := by
    refine ⟨le_top, Q.isPGroup', ?_⟩
    change ¬ 2 ∣ (Q : Subgroup X).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  obtain ⟨m, hdvd⟩ := card_dvd_of_sylow_le hm hQ le_sup_right hM
  have hR : Nat.card R ∣ 63 * 2 ^ m := (Subgroup.card_dvd_of_le le_sup_left).trans hdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.2 hodd even_two
  have key : ∀ k : ℕ, p ^ k ∣ Nat.card X → ¬ p ^ k ∣ 63 → False := by
    intro k hk h63
    have h2 : Nat.Coprime (p ^ k) (2 ^ m) :=
      Nat.Coprime.pow k m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    exact h63 (h2.dvd_of_dvd_mul_right ((R.pow_dvd_card_of_pow_dvd_card hk).trans hR))
  rw [hcard] at hpX
  rcases (Nat.Prime.dvd_mul hp).1 hpX with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
        exact key 4 (by rw [hcard]; norm_num) (by norm_num)
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h)
      exact key 2 (by rw [hcard]; norm_num) (by norm_num)
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    exact key 1 (by rw [hcard]; norm_num) (by norm_num)

end CFSG.Quasithin.H13.D42
