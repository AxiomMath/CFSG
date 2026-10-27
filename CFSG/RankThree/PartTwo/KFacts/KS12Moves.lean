module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped IsMulCommutative

theorem not_isMulCommutative_sylow_of_perfect {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hX : commutator X = ⊤) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = p) (S : Sylow p X) : ¬ IsMulCommutative (S : Subgroup X) := by
  intro hS
  have : IsMulCommutative (S : Subgroup X) := hS
  have hzS : z ∈ (S : Subgroup X) := by
    have hN : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
    have hP : IsPGroup p (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
    exact hP.le_sylow_of_normal S (Subgroup.mem_zpowers z)
  set ϕ := MonoidHom.transfer (MonoidHom.id (S : Subgroup X)) with hϕ
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup X) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have hzk : z ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ hz k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hzk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup X)) z key
  have h2 : ϕ z = 1 := by
    have hzc : z ∈ commutator X := hX ▸ Subgroup.mem_top z
    exact Abelianization.commutator_subset_ker ϕ hzc
  rw [h2] at h1
  have h3 : z ^ (S : Subgroup X).index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hzp] at h4
  exact S.not_dvd_index h4

theorem exists_normalizer_moves_of_factorization {X : Type*} [Group X] [Finite X]
    (hX : commutator X = ⊤) (hZ : Nat.card (Subgroup.center X) = 3)
    (h27 : (Nat.card X).factorization 3 = 3) (T : Subgroup X) (hT9 : Nat.card T = 9) :
    ∃ x ∈ Subgroup.normalizer (T : Set X), IsPGroup 3 (Subgroup.zpowers x) ∧
      ∃ t ∈ T, x * t * x⁻¹ ≠ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 (by rw [hZ])
  have hzZ : (z : X) ∈ Subgroup.center X := z.2
  have hz3 : orderOf (z : X) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  obtain ⟨S, hTS⟩ := hT3.exists_le_sylow
  have hS27 : Nat.card (S : Subgroup X) = 27 := by
    rw [Sylow.card_eq_multiplicity, h27]
    norm_num
  have hSnc := not_isMulCommutative_sylow_of_perfect hX hzZ hz3 S
  set T' : Subgroup (S : Subgroup X) := T.subgroupOf S with hT'
  have hT'card : Nat.card T' = 9 := by
    rw [← hT9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv
  have hidx : T'.index = 3 := by
    have h := T'.card_mul_index
    rw [hT'card, hS27] at h
    omega
  have hT'n : T'.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hidx, hS27]
    norm_num)
  by_contra hcon
  push Not at hcon
  have hcent : ∀ s : (S : Subgroup X), ∀ t ∈ T, (s : X) * t * (s : X)⁻¹ = t := by
    intro s t ht
    have hsN : (s : X) ∈ Subgroup.normalizer (T : Set X) := by
      refine Subgroup.mem_normalizer_fintype fun u hu => ?_
      have hu' : (⟨u, hTS hu⟩ : (S : Subgroup X)) ∈ T' := Subgroup.mem_subgroupOf.mpr hu
      have := hT'n.conj_mem _ hu' s
      exact Subgroup.mem_subgroupOf.mp this
    exact hcon s hsN (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr s.2)) t ht
  have hker : (QuotientGroup.mk' T').ker ≤ Subgroup.center (S : Subgroup X) := by
    rw [QuotientGroup.ker_mk']
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have h := hcent s t (Subgroup.mem_subgroupOf.mp ht)
    change (s : X) * t = t * s
    calc (s : X) * t = ((s : X) * t * (s : X)⁻¹) * s := by group
      _ = t * s := by rw [h]
  have hQ : Nat.card ((S : Subgroup X) ⧸ T') = 3 := by
    rw [← Subgroup.index_eq_card, hidx]
  have : IsCyclic ((S : Subgroup X) ⧸ T') := isCyclic_of_prime_card hQ
  exact hSnc (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' T') hker)

theorem factorization_three_mul_nine_mul {k : ℕ} (hk : ¬ 3 ∣ k) :
    (3 * (9 * k)).factorization 3 = 3 := by
  have hk0 : k ≠ 0 := fun h => hk (h ▸ dvd_zero 3)
  rw [show 3 * (9 * k) = 3 ^ 3 * k by ring, Nat.factorization_mul (by positivity) hk0,
    Finsupp.add_apply, Nat.prime_three.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hk, add_zero]

theorem card_of_isTripleCover {X Y : Type*} [Group X] [Group Y] [Finite X]
    (h : Sec4.IsTripleCover X Y) : Nat.card X = 3 * Nat.card Y := by
  obtain ⟨hZ, ⟨e⟩⟩ := h
  rw [← hZ, ← Nat.card_congr e.toEquiv, mul_comm]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X))

theorem exists_normalizer_moves_of_isTripleCover_alt {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X)
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)))
    (T : Subgroup X) (hT9 : Nat.card T = 9) :
    ∃ x ∈ Subgroup.normalizer (T : Set X), IsPGroup 3 (Subgroup.zpowers x) ∧
      ∃ t ∈ T, x * t * x⁻¹ ≠ t := by
  have hp : commutator X = ⊤ := by
    have h := hq.1
    rwa [Group.isPerfect_def] at h
  rcases hX with h6 | h7
  · have hcard := card_of_isTripleCover h6
    rw [nat_card_alternatingGroup, Nat.card_fin] at hcard
    refine exists_normalizer_moves_of_factorization hp h6.1 ?_ T hT9
    rw [hcard, show Nat.factorial 6 / 2 = 9 * 40 by decide]
    exact factorization_three_mul_nine_mul (by norm_num)
  · have hcard := card_of_isTripleCover h7
    rw [nat_card_alternatingGroup, Nat.card_fin] at hcard
    refine exists_normalizer_moves_of_factorization hp h7.1 ?_ T hT9
    rw [hcard, show Nat.factorial 7 / 2 = 9 * 280 by decide]
    exact factorization_three_mul_nine_mul (by norm_num)

end CFSG.RankThree.PartTwo.KFacts
