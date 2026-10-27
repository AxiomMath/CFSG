module

public import CFSG.Quasithin.EmptyFaithful.T1515cB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Y1Quot

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem three_dvd_card_of_type {X : Subgroup G}
    (htype : IsAltType X 3 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type X n) : 3 ∣ Nat.card X := by
  rcases htype with ⟨α, hαs, -⟩ | ⟨n, hn, F, hFf, hFfin, hcard, α, hαs, -⟩
  · have h := Subgroup.card_dvd_of_surjective hαs
    rwa [S15221.card_alternatingGroup_three] at h
  · have h := Subgroup.card_dvd_of_surjective hαs
    refine dvd_trans ?_ h
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hcard]
    refine Dvd.dvd.mul_left ?_ _
    have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 n

theorem card_conjByElt (g : G) (X : Subgroup G) : Nat.card (conjByElt g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem not_three_blocks [Finite G] {I A B C : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hA : IsBlock2 I A) (hB : IsBlock2 I B)
    (hC : IsBlock2 I C) (h3A : 3 ∣ Nat.card A) (h3B : 3 ∣ Nat.card B) (h3C : 3 ∣ Nat.card C)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : False :=
  CFSG.QuasithinUnique.L238.three_blocks_false_cat hrank hA.2.1 hB.2.1 hC.2.1
    ⟨hA.1.2.1, hB.1.2.1, hC.1.2.1⟩ ⟨h3A, h3B, h3C⟩ hAB hAC hBC
    ⟨hC19 I A B hchar hA hB hAB, hC19 I A C hchar hA hC hAC, hC19 I B C hchar hB hC hBC⟩

theorem oTwoUpper_le_normalizer_of_block [Finite G] {I X K : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hX : IsBlock2 I X) (h3 : 3 ∣ Nat.card X)
    (hKI : K ≤ I) : oTwoUpper K ≤ Subgroup.normalizer (X : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxK, hxo⟩
  show x ∈ Subgroup.normalizer (X : Set G)
  by_contra hxn
  have hxI : x ∈ I := hKI hxK
  have hY₁ : IsBlock2 I (conjByElt x X) :=
    isBlock2_conjByElt_of_normalizer1515c hX (Subgroup.le_normalizer hxI)
  have hY₂ : IsBlock2 I (conjByElt (x * x) X) :=
    isBlock2_conjByElt_of_normalizer1515c hX (Subgroup.le_normalizer (mul_mem hxI hxI))
  have hXY₁ : X ≠ conjByElt x X := fun h =>
    hxn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hXY₂ : X ≠ conjByElt (x * x) X := by
    intro h
    apply hxn
    have hxx : x * x ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
    obtain ⟨t, ht⟩ := hxo
    have hpow : x ^ (2 * t + 1) = 1 := by rw [← ht]; exact pow_orderOf_eq_one x
    have : x = (x * x) ^ (t + 1) := by
      have h1 : (x * x) ^ (t + 1) = x ^ (2 * t + 2) := by
        rw [← pow_two, ← pow_mul]; ring_nf
      rw [h1, pow_succ, hpow, one_mul]
    rw [this]
    exact Subgroup.pow_mem _ hxx _
  have hY₁₂ : conjByElt x X ≠ conjByElt (x * x) X := by
    intro h
    apply hXY₁
    have h1 : conjByElt (x * x) X = conjByElt x (conjByElt x X) := conjSub_mul x x X
    rw [h1] at h
    have h2 : conjByElt x (conjByElt x X) = conjByElt x X := h.symm
    exact ((conjSub_inj x).mp (show conjSub x (conjByElt x X) = conjSub x X from h2)).symm
  exact not_three_blocks hC19 hchar hrank hX hY₁ hY₂ h3 (by rw [card_conjByElt]; exact h3)
    (by rw [card_conjByElt]; exact h3) hXY₁ hXY₂ hY₁₂

end CFSG.Quasithin.S15223
