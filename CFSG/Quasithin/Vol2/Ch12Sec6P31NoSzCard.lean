module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31a

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31
open scoped IsMulCommutative

section L1

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem card_L1_two_three (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ∃ i j : ℕ, Nat.card ↥(S126.Li L F.V1) = 2 ^ i * 3 ^ j := by
  obtain ⟨a, ha⟩ := S126L19a.card_inf_eq_pow h1222 hH (S126L19b.L1_le_L F)
  have hcard := S126L19a.card_eq F hH (S126L19b.L1_le_L F)
  change Nat.card (S126.Li L F.V1) =
    Nat.card (S126L19b.L1bar F hH) * Nat.card ↥(S126.Li L F.V1 ⊓
      Subgroup.centralizer (V : Set G)) at hcard
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card (S126L19b.L1bar F hH) → r = 2 ∨ r = 3 := by
    intro r hr hdvd
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := S126L19b.L1bar F hH) r hdvd
    have h24 : ((σ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) ^ 24 = 1 :=
      S126L19a.pow_24 (S126L19b.blocks_of_mem_L1bar F hH σ.2)
    have hσ24 : (σ : S126L19b.L1bar F hH) ^ 24 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h24
    have h24dvd : r ∣ 24 := by
      rw [← hσ]
      exact orderOf_dvd_of_pow_eq_one hσ24
    have h24' : r ∣ 2 ^ 3 * 3 ^ 1 := by
      rw [show (2 : ℕ) ^ 3 * 3 ^ 1 = 24 by norm_num]
      exact h24dvd
    rcases hr.dvd_mul.mp h24' with h2dvd | h3dvd
    · obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2dvd
      interval_cases j
      · rw [hj] at hr
        exact absurd hr (by norm_num)
      · left
        rw [hj]
        norm_num
      · rw [hj] at hr
        exact absurd hr (by norm_num)
      · rw [hj] at hr
        exact absurd hr (by norm_num)
    · have h3 : r = 1 ∨ r = 3 := (Nat.dvd_prime Nat.prime_three).1 h3dvd
      rcases h3 with h1 | h3
      · exact absurd h1 hr.ne_one
      · exact Or.inr h3
  have hfac : Nat.card (S126L19b.L1bar F hH) =
      2 ^ (Nat.card (S126L19b.L1bar F hH)).factorization 2 *
        3 ^ (Nat.card (S126L19b.L1bar F hH)).factorization 3 := by
    have hn0 : Nat.card (S126L19b.L1bar F hH) ≠ 0 := Nat.card_pos.ne'
    have hsub : (Nat.card (S126L19b.L1bar F hH)).factorization.support ⊆ {2, 3} := by
      intro r hr
      rw [Nat.support_factorization] at hr
      have h := hprime r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
      simpa using h
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
    rw [Finsupp.prod_of_support_subset _ hsub _ (by simp), Finset.prod_pair (by norm_num)]
  set b := (Nat.card (S126L19b.L1bar F hH)).factorization 2
  set c := (Nat.card (S126L19b.L1bar F hH)).factorization 3
  have hfac' : Nat.card (S126L19b.L1bar F hH) = 2 ^ b * 3 ^ c := hfac
  refine ⟨b + a, c, ?_⟩
  calc Nat.card (S126.Li L F.V1)
      = Nat.card (S126L19b.L1bar F hH) *
          Nat.card ↥(S126.Li L F.V1 ⊓ Subgroup.centralizer (V : Set G)) := hcard
    _ = (2 ^ b * 3 ^ c) * 2 ^ a := by rw [hfac', ha]
    _ = 2 ^ (b + a) * 3 ^ c := by rw [pow_add]; ring

end L1

section Join

variable {G : Type} [Group G] [Finite G]

theorem card_sup_dvd {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card ↥A * Nat.card ↥B := by
  set X : Subgroup G := A ⊔ B with hX
  have hAX : A ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXN : X ≤ Subgroup.normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer hB
  haveI hAn : (A.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).2 hXN
  have h1 : (A.subgroupOf X) ⊔ (B.subgroupOf X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAX hBX]
    exact Subgroup.subgroupOf_self _
  have h2 : (A.subgroupOf X).relIndex (B.subgroupOf X ⊔ A.subgroupOf X) =
      (A.subgroupOf X).relIndex (B.subgroupOf X) := Subgroup.relIndex_sup_right _ _
  rw [sup_comm, h1, Subgroup.relIndex_top_right] at h2
  have h3 : (A.subgroupOf X).index ∣ Nat.card ↥(B.subgroupOf X) := by
    rw [h2]
    exact Subgroup.relIndex_dvd_card _ _
  have h4 : Nat.card ↥(A.subgroupOf X) * (A.subgroupOf X).index = Nat.card ↥X :=
    Subgroup.card_mul_index _
  have hA : Nat.card ↥(A.subgroupOf X) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  have hB' : Nat.card ↥(B.subgroupOf X) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  rw [hB'] at h3
  rw [← h4, hA]
  exact Nat.mul_dvd_mul_left _ h3

end Join

section Star

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem card_star_L1T_dvd (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {H : Subgroup G} (hTH : T ≤ H) (hL1H : Li L F.V1 ≤ H) (hT2 : IsPGroup 2 T) :
    ∃ i j : ℕ, Nat.card ↥(star H (Li L F.V1 ⊔ T)) ∣ 2 ^ i * 3 ^ j := by
  obtain ⟨i, j, hij⟩ := card_L1_two_three h1222 F hH
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hdvd := card_sup_dvd (A := Li L F.V1) (B := T) (S126L19b.T_le_normalizer_L1 h1222 hH)
  rw [hij, hk] at hdvd
  have hX : Li L F.V1 ⊔ T ≤ H := sup_le hL1H hTH
  let f : ↥((Li L F.V1 ⊔ T).subgroupOf H) →* ↥(star H (Li L F.V1 ⊔ T)) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap ((Li L F.V1 ⊔ T).subgroupOf H)
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  have h1 : Nat.card ↥(star H (Li L F.V1 ⊔ T)) ∣ Nat.card ↥((Li L F.V1 ⊔ T).subgroupOf H) :=
    Subgroup.card_dvd_of_surjective (f := f) hf
  have h2 : Nat.card ↥((Li L F.V1 ⊔ T).subgroupOf H) = Nat.card ↥(Li L F.V1 ⊔ T) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rw [h2] at h1
  refine ⟨i + k, j, ?_⟩
  have := h1.trans hdvd
  rw [show 2 ^ i * 3 ^ j * 2 ^ k = 2 ^ (i + k) * 3 ^ j by rw [pow_add]; ring] at this
  exact this

theorem isThreeGroup_of_odd_le_star (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {H : Subgroup G} (hTH : T ≤ H) (hL1H : Li L F.V1 ≤ H)
    (hT2 : IsPGroup 2 T) {D : Subgroup (HStar H)} (hD : D ≤ star H (Li L F.V1 ⊔ T))
    (hodd : Odd (Nat.card D)) : ∀ d ∈ D, ∃ k : ℕ, d ^ 3 ^ k = 1 := by
  obtain ⟨i, j, hdvd⟩ := card_star_L1T_dvd h1222 F hH hTH hL1H hT2
  have h1 : Nat.card ↥D ∣ 2 ^ i * 3 ^ j := (Subgroup.card_dvd_of_le hD).trans hdvd
  have hcop2 : Nat.Coprime 2 (Nat.card ↥D) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h =>
      (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hcop : Nat.Coprime (Nat.card ↥D) (2 ^ i) := (Nat.Coprime.pow_left i hcop2).symm
  have h2 : Nat.card ↥D ∣ 3 ^ j := hcop.dvd_of_dvd_mul_left h1
  intro d hd
  refine ⟨j, ?_⟩
  have h3 : orderOf (⟨d, hd⟩ : ↥D) ∣ 3 ^ j := (orderOf_dvd_natCard _).trans h2
  have h4 : (⟨d, hd⟩ : ↥D) ^ 3 ^ j = 1 := orderOf_dvd_iff_pow_eq_one.1 h3
  have h5 := congrArg Subtype.val h4
  simpa using h5

end Star

end CFSG.Quasithin.H13.P31Sz
