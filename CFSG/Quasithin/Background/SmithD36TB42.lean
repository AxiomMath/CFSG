module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42
public import CFSG.Quasithin.EmptyFaithful.A38cOrders
public import CFSG.Quasithin.H13.VolIA38SLThree
public import CFSG.Quasithin.Vol2.Ch10SecQ1Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA

variable {V : Type} [CommGroup V] [Finite V]

theorem b42_card_two_of_a38Types
    (hV : ∀ v : V, v ^ 2 = 1) {G L A : Subgroup (MulAut V)} (hB : B4Hyp G L)
    (hA : IsFFStarOffender G A) (hA2 : Nat.card ↥A = 2) (hc : B42Conclusion G L A)
    (hL : A38Types ↥L) [hs : IsSimpleGroup ↥L] :
    BinaryNaturalSL L ⊤ ⊥ 3 1 ∨ AlternatingNatural L ⊤ ⊥ 5 := by
  have hcard : A38Order (Nat.card ↥L) := a38Order_card hL
  have hnc := InternalSec.exists_noncomm_of_isQuasisimple hB.2.2.1
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  have hnt : Nontrivial ↥L := hs.toNontrivial
  have card_false : ∀ {N : ℕ}, Nat.card ↥L = N → ¬ A38Order N → False :=
    fun hN hnot => hnot (hN ▸ hcard)
  have hrk : rk ↥A = 1 := by
    unfold rk
    rw [hA2]
    simp
  have one_le : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n → 1 ≤ n := by
    intro K _ _ n hK
    by_contra h
    have h0 : n = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  rcases hc with ⟨-, ⟨n, hnat⟩, hsyl, -⟩ | ⟨-, ⟨n, hnat⟩, -⟩ | ⟨⟨n, hsp, hJ⟩, -⟩ |
      ⟨⟨n, -, hrk4, -⟩, -⟩ | h5 | ⟨-, -, hrk6, -⟩ | ⟨-, -, ⟨α, π, hR⟩, -⟩ |
      ⟨-, -, -, K, _, _, Γ₀, -, -, hhat, -, π, hR, -⟩ | ⟨-, n, hn, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩ |
      ⟨-, -, -, -, π, hR, -⟩
  ·
    exfalso
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 := one_le hFc
    obtain ⟨hAL, -, hodd⟩ := hsyl
    have hLc : Nat.card ↥L = 2 * (A.subgroupOf L).index := by
      have h := Subgroup.card_mul_index (A.subgroupOf L)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA2] at h
      exact h.symm
    have hLc2 : Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_two_pow hFc]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact CFSG.QuasithinUnique.Bridge.TypeList.commutator_ne_top_of_card_six
        (by rw [hLc2]; norm_num) hB.2.2.1.1.commutator_eq_top
    · apply hodd
      have h4 : 4 ∣ 2 * (A.subgroupOf L).index := by
        rw [← hLc, hLc2]
        exact Dvd.dvd.mul_right (dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 h2)) _
      omega
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hn1 : n = 1 := a38TypesSLThree_holds ↥L F n hFc ⟨e.symm⟩ hL
    subst hn1
    exact Or.inl hnat
  ·
    exfalso
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hsp.exists_equiv
    have h1 := one_le hFc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have hLJ := le_ffJ_of_two_dvd hV hB (two_dvd_card_ffJ hA)
      obtain ⟨N, hN, ⟨eN⟩⟩ := exists_normal_of_equiv e hLJ ((B6.ffJ_le G).trans hGL)
      have hq : CFSG.IsQuasisimple ↥N :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hB.2.2.1
      have h360 := factSp4TwoNormal_holds F (by rw [hFc]; norm_num) N hN hq
      exact card_false (by rw [← Nat.card_congr eN.toEquiv, h360]) not_a38Order_360
    · have hJL := hJ (by omega)
      rw [hJL] at e
      refine a38Order_not_rankTwoOrder hcard
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h1, ?_⟩))))
      rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hFc, ordBC_two_two_pow h1, ← pow_mul,
        ← pow_mul, mul_comm n 4, mul_comm n 2]
  ·
    exfalso
    omega
  ·
    obtain ⟨m, hm, halt, ⟨e⟩⟩ := InternalSec.alternatingNatural_of_b42Case5 hV hB h5
    rcases hm with rfl | rfl
    · exact Or.inr halt
    · refine (card_false ?_ not_a38Order_2520).elim
      rw [Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)]
      decide
  ·
    exfalso
    omega
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π
      hR.1
    refine (card_false ?_ not_a38Order_2520).elim
    rw [← Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)]
    decide
  ·
    exfalso
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  ·
    exfalso
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    rcases hn with rfl | rfl
    · refine card_false ?_ not_a38Order_20160
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_of_two hF2]
    · refine card_false ?_ not_a38Order_9999360
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_of_two hF2]
  ·
    exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 4) (by norm_num)) π hR.1
    refine card_false ?_ not_a38Order_20160
    rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_two]
  ·
    exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 5) (by norm_num)) π hR.1
    refine card_false ?_ not_a38Order_9999360
    rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_two]

end CFSG.Quasithin
