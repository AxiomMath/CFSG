module

public import CFSG.Quasithin.EmptyFaithful.A38c8Defs
public import CFSG.Quasithin.EmptyFaithful.A38c8Out
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.Exceptional

theorem card_of_isSporadic_m24 {X : Type} [Group X]
    (h : IsSporadic .M24 X) : Nat.card X = 244823040 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M24

theorem center_eq_bot_of_isSporadic_m24 {X : Type} [Group X]
    (h : IsSporadic .M24 X) : Subgroup.center X = ⊥ := by
  have hc := card_of_isSporadic_m24 h
  obtain ⟨e⟩ := h
  have hs0 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hs : IsSimpleGroup X := e.isSimpleGroup
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.1 h1
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [hc] at hp
    norm_num at hp

theorem odd_card_outer_of_isSporadic_m24 (hOut : OutOddM24) {X : Type} [Group X]
    (h : IsSporadic .M24 X) :
    Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact hOut

theorem card_of_isExt_e16_l42 {X : Type} [Group X]
    (h : IsExt X (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 4 2 1 Y')) : Nat.card X = 322560 := by
  obtain ⟨V, hVn, ⟨e⟩, ⟨-, K, _, _, hK, ⟨f⟩⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hV : Nat.card V = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
    simp
  have hQ : Nat.card (X ⧸ V) = 20160 := by
    rw [Nat.card_congr f.toEquiv,
      Nat.card_congr ((statedProjStatedSLEquivOfCardTwo hK2 4).trans
        (glEquivZModTwoOfCardTwo hK2 4)).toEquiv, card_GL_four_two]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, hQ, hV]

theorem exists_isSylowTwoOf_le_of_factorization_le {Y : Type} [Group Y] [Finite Y]
    {N B : Subgroup Y} (hBN : B ≤ N)
    (h : (Nat.card N).factorization 2 ≤ (Nat.card B).factorization 2) :
    ∃ P : Subgroup Y, P ≤ B ∧ IsSylowTwoOf P N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥B) := inferInstance
  have hPB : (P₀ : Subgroup ↥B).map B.subtype ≤ B := Subgroup.map_subtype_le _
  have hPN : (P₀ : Subgroup ↥B).map B.subtype ≤ N := hPB.trans hBN
  have hcard : Nat.card ↥((P₀ : Subgroup ↥B).map B.subtype) =
      2 ^ (Nat.card B).factorization 2 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, P₀.card_eq_multiplicity]
  refine ⟨_, hPB, hPN, IsPGroup.of_card hcard, ?_⟩
  rintro ⟨j, hj⟩
  have h1 : Nat.card ↥(((P₀ : Subgroup ↥B).map B.subtype).subgroupOf N) =
      2 ^ (Nat.card B).factorization 2 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  have h2 := Subgroup.card_mul_index (((P₀ : Subgroup ↥B).map B.subtype).subgroupOf N)
  rw [h1, hj] at h2
  have hdvd : 2 ^ ((Nat.card B).factorization 2 + 1) ∣ Nat.card N := by
    refine ⟨j, ?_⟩
    rw [← h2, pow_succ]
    ring
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 hdvd
  omega

theorem inner_of_m24 (hOut : OutOddM24) {Y : Type} [Group Y]
    [Finite Y] {N T B : Subgroup Y} (hN : N.Normal) (hM : IsSporadic .M24 ↥N)
    (hT : IsSylowTwoOf T ⊤) (hBN : B ≤ N)
    (hBe : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 4 2 1 Y'))
    (hTB : T ≤ Subgroup.normalizer (B : Set Y)) : ∀ t ∈ T, InnerOnModO2 B t := by
  intro t ht
  have hcN : Nat.card N = 2 ^ 10 * 239085 := by
    rw [card_of_isSporadic_m24 hM]
    norm_num
  have hcB : Nat.card B = 2 ^ 10 * 315 := by
    rw [card_of_isExt_e16_l42 hBe]
    norm_num
  have h2 : ((2 : ℕ) ^ 10).factorization 2 = 10 := by
    rw [Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hfac : (Nat.card N).factorization 2 ≤ (Nat.card B).factorization 2 := by
    rw [hcN, hcB, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply, h2,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 239085),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  obtain ⟨P, hPB, hP⟩ := exists_isSylowTwoOf_le_of_factorization_le hBN hfac
  obtain ⟨x, hxTN, hconj⟩ := exists_mem_inf_inner_of_odd_outer hN hT
    (center_eq_bot_of_isSporadic_m24 hM) (odd_card_outer_of_isSporadic_m24 hOut hM) t ht
  have hxT : x ∈ T := (Subgroup.mem_inf.1 hxTN).1
  have hxN : x ∈ N := (Subgroup.mem_inf.1 hxTN).2
  have hZ : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    hT.2.1.to_le ((Subgroup.zpowers_le).2 hxT)
  have hle : Subgroup.zpowers x ≤ B :=
    FLc.le_of_normalizes_of_sylow hP hPB hBN ((Subgroup.zpowers_le).2 hxN) hZ
      ((Subgroup.zpowers_le).2 (hTB hxT))
  refine ⟨x, hle (Subgroup.mem_zpowers x), fun y hy => ?_⟩
  rw [hconj y (hBN hy), inv_mul_cancel]
  exact Subgroup.one_mem _

end CFSG.Quasithin.A38c8
