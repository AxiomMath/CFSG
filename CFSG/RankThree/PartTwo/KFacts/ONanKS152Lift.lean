module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS152

open CFSG.RankThree.PartTwo

theorem exists_lift_nine_aux {L : Type*} [Group L] [Finite L] (θ : Subgroup L) [θ.Normal]
    (hθ3 : ¬ 3 ∣ Nat.card θ) (E₀ : Subgroup (L ⧸ θ)) (h9 : Nat.card E₀ = 9)
    (h3 : ∀ x ∈ E₀, x ^ 3 = 1) :
    ∃ E : Subgroup L, Nat.card E = 9 ∧ Disjoint E θ ∧ ∀ x ∈ E, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E' : Subgroup L := E₀.comap (QuotientGroup.mk' θ) with hE'
  have hsurj : Function.Surjective ((QuotientGroup.mk' θ).subgroupComap E₀) :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective θ)
  have hdvd : 3 ^ 2 ∣ Nat.card E' := by
    have h : Nat.card E₀ ∣ Nat.card E' := Subgroup.card_dvd_of_surjective hsurj
    rw [h9] at h
    simpa using h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  have hKcard : Nat.card (K.map E'.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective E'.subtype_injective, hK]; norm_num
  have hdisj : Disjoint (K.map E'.subtype) θ := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hKcard]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
  refine ⟨K.map E'.subtype, hKcard, hdisj, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxE : (x : L) ∈ E' := x.2
  have hx3 : ((x : L) ^ 3 : L) ∈ θ := by
    have h := h3 _ hxE
    rw [← map_pow] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  have hmem : ((x : L) ^ 3 : L) ∈ K.map E'.subtype := ⟨x ^ 3, pow_mem hx 3, rfl⟩
  exact Subgroup.mem_bot.mp (hdisj.le_bot ⟨hmem, hx3⟩)

theorem exists_nine_exp_three
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ E₀ : Subgroup X, Nat.card E₀ = 9 ∧ ∀ x ∈ E₀, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  have h415 := Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415
  obtain ⟨-, h27, hexp⟩ := hHeis
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(P : Subgroup X)) 3 (n := 2)
    (by rw [h27]; norm_num)
  refine ⟨K.map (P : Subgroup X).subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective, hK]; norm_num
  · rintro _ ⟨x, -, rfl⟩
    have h := Monoid.pow_exponent_eq_one x
    rw [hexp] at h
    simpa using congrArg Subtype.val h

theorem exists_lift_nine
    {L : Type} [Group L] [Finite L]
    (θ : Subgroup L) [θ.Normal] (hθ3 : ¬ 3 ∣ Nat.card θ)
    (he : Nonempty (L ⧸ θ ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ E : Subgroup L, Nat.card E = 9 ∧ Disjoint E θ ∧ ∀ x ∈ E, x ^ 3 = 1 := by
  obtain ⟨E₀, h9, h3⟩ := exists_nine_exp_three he
  exact exists_lift_nine_aux θ hθ3 E₀ h9 h3

end CFSG.RankThree.PartTwo.KFacts.KS152
