module

public import CFSG.Permutation.FiveTransitive.Degree24OrbitDivisibility

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem thirteen_dvd_of_degree24_support_ten_incidence
    {a b : ℕ}
    (h : 5100480 * a = b * 240240) :
    13 ∣ a := by
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

private theorem three_dvd_of_degree24_support_fifteen_incidence
    {a b : ℕ}
    (h : 5100480 * a = b * 15120) :
    3 ∣ a := by
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

private theorem no_small_degree24_order_five_support_partition
    {a b : ℕ}
    (hPartition : 4 = a + b)
    (hThirteen : 13 ∣ a) (hThree : 3 ∣ b) :
    False := by
  obtain ⟨c, hc⟩ := hThirteen
  obtain ⟨d, hd⟩ := hThree
  omega

private theorem degree24_order_five_support_fifteen_card
    {a b : ℕ}
    (hPartition : 224 = a + b)
    (hThirteen : 13 ∣ a) (hFourA : 4 ∣ a)
    (hThree : 3 ∣ b) (hFourB : 4 ∣ b) :
    b = 120 := by
  obtain ⟨c₁, hc₁⟩ := hThirteen
  obtain ⟨c₂, hc₂⟩ := hFourA
  obtain ⟨d₁, hd₁⟩ := hThree
  obtain ⟨d₂, hd₂⟩ := hFourB
  omega

private theorem degree24_global_support_fifteen_card
    {a : ℕ}
    (h : 5100480 * 120 = a * 15120) :
    a = 40480 := by
  omega

private theorem dvd_four_hundred_three_thousand_two_hundred
    {k : ℕ}
    (hGroup : k ∣ 1428134400)
    (hCentralizer : k ∣ 272160000) :
    k ∣ 403200 := by
  have hGcd := Nat.dvd_gcd hGroup hCentralizer
  norm_num at hGcd ⊢
  exact hGcd

theorem five_point_stabilizer_card_ne_two_hundred_eighty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 280 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  intro hHcard
  have hP5 :
      MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hPcardExact :
      Nat.card P = 1428134400 := by
    rw [hPcard, hHcard]
  let S : Sylow 5 H := Sylow.nonempty.some
  have hScard : Nat.card S = 5 :=
    sylow_five_card_eq_five_of_card_eq_five_mul
      H 56 (by norm_num) (by norm_num)
        (by simpa using hHcard) S
  have hSindex : S.index = 56 := by
    have hproduct := S.index_mul_card
    rw [hScard, hHcard] at hproduct
    omega
  let n := Nat.card (Sylow 5 H)
  have hnDvd : n ∣ 56 := by
    have hdiv := S.card_dvd_index
    change n ∣ S.index at hdiv
    simpa [hSindex] using hdiv
  have hnMod : n % 5 = 1 := by
    have hmod := card_sylow_modEq_one 5 H
    change n % 5 = 1 % 5 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  have hnLe : n ≤ 56 :=
    Nat.le_of_dvd (by norm_num) hnDvd
  have hnCases : n = 1 ∨ n = 56 := by
    have hfinite :
        ∀ q : Fin 57,
          q.1 ∣ 56 →
            q.1 % 5 = 1 →
              q.1 = 1 ∨ q.1 = 56 := by
      decide
    exact hfinite ⟨n, by omega⟩ hnDvd hnMod
  have hAllCard :
      Nat.card {u : H // orderOf u = 5} =
        n * 4 := by
    simpa only [n] using
      card_order_five_elements_of_sylow_card_five
        H S hScard
  have hSupport
      (u : fixingSubgroup P s)
      (hu : orderOf u = 5) :
      ((((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = 10) ∨
        ((((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = 15) :=
    order_five_mem_five_stabilizer_support_eq_ten_or_fifteen
      X P hcard h5 hnotAlt s hs u hu
  have hPartition :=
    Nat.card_congr
      (localOrderFiveElementsSupportEquiv
        X P s hSupport)
  rw [Nat.card_sum, hAllCard] at hPartition
  have hFourTen :
      4 ∣
        Nat.card
          (LocalOrderFiveSupportElements
            X P s 10) :=
    four_dvd_card_localOrderFiveSupportElements
      X P s 10 S hScard
  have hFourFifteen :
      4 ∣
        Nat.card
          (LocalOrderFiveSupportElements
            X P s 15) :=
    four_dvd_card_localOrderFiveSupportElements
      X P s 15 S hScard
  letI : Fintype s := Fintype.ofFinite s
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hs]
  let es : s ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hsCard
  let e₀ : Fin 5 ↪ X := {
    toFun := fun i => (es.symm i).1
    inj' := by
      intro i j hij
      apply es.symm.injective
      exact Subtype.ext hij }
  have he₀Range : Set.range e₀ = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hLocalTen :
      Nat.card
          (LocalOrderFiveSupportElements
            X P s 10) =
        Nat.card
          (OrderFiveSupportFixesEmbedding
            X P 10 e₀) :=
    Nat.card_congr
      (localOrderFiveSupportEquiv
        X P s 10 e₀ he₀Range)
  have hLocalFifteen :
      Nat.card
          (LocalOrderFiveSupportElements
            X P s 15) =
        Nat.card
          (OrderFiveSupportFixesEmbedding
            X P 15 e₀) :=
    Nat.card_congr
      (localOrderFiveSupportEquiv
        X P s 15 e₀ he₀Range)
  have hfixedTen
      (u : OrderFiveSupportElements X P 10) :
      Nat.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
        240240 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
          (Fintype.card
            (MulAction.fixedBy X u.1)).descFactorial
              (Fintype.card (Fin 5)) :=
        Degree15.card_fixedBy_embedding
          (G := P) (X := X) (I := Fin 5) u.1
      _ = 240240 := by
        rw [Degree15.card_fixedBy_subgroup_perm,
          hcard, u.2.2, Fintype.card_fin]
        norm_num [Nat.descFactorial]
  have hfixedFifteen
      (u : OrderFiveSupportElements X P 15) :
      Nat.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
        15120 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
          (Fintype.card
            (MulAction.fixedBy X u.1)).descFactorial
              (Fintype.card (Fin 5)) :=
        Degree15.card_fixedBy_embedding
          (G := P) (X := X) (I := Fin 5) u.1
      _ = 15120 := by
        rw [Degree15.card_fixedBy_subgroup_perm,
          hcard, u.2.2, Fintype.card_fin]
        norm_num [Nat.descFactorial]
  have hEcard : Nat.card (Fin 5 ↪ X) = 5100480 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq,
      Fintype.card_fin, hcard]
    norm_num [Nat.descFactorial]
  have hcountTen :=
    orderFiveSupport_incidence_count
      X P hP5 10 240240 hfixedTen e₀
  rw [hEcard, ← hLocalTen] at hcountTen
  have hcountFifteen :=
    orderFiveSupport_incidence_count
      X P hP5 15 15120 hfixedFifteen e₀
  rw [hEcard, ← hLocalFifteen] at hcountFifteen
  have hThirteen :
      13 ∣ Nat.card
        (LocalOrderFiveSupportElements X P s 10) := by
    exact
      thirteen_dvd_of_degree24_support_ten_incidence
        hcountTen
  have hThree :
      3 ∣ Nat.card
        (LocalOrderFiveSupportElements X P s 15) := by
    exact
      three_dvd_of_degree24_support_fifteen_incidence
        hcountFifteen
  rcases hnCases with hnOne | hnFiftySix
  · rw [hnOne] at hPartition
    exact
      no_small_degree24_order_five_support_partition
        hPartition hThirteen hThree
  · rw [hnFiftySix] at hPartition
    have hLocalFifteenCard :
        Nat.card
            (LocalOrderFiveSupportElements
              X P s 15) =
          120 := by
      exact
        degree24_order_five_support_fifteen_card
          hPartition hThirteen hFourTen
            hThree hFourFifteen
    have hGlobalFifteenCard :
        Nat.card
            (OrderFiveSupportElements X P 15) =
          40480 := by
      rw [hLocalFifteenCard] at hcountFifteen
      exact
        degree24_global_support_fifteen_card
          hcountFifteen
    have hConjActCardExact :
        Nat.card (ConjAct P) =
          1428134400 := by
      rw [Nat.card_eq_fintype_card,
        ConjAct.card,
        ← Nat.card_eq_fintype_card,
        hPcardExact]
    have hStabilizerDvd
        (u : OrderFiveSupportElements X P 15) :
        Nat.card
            (MulAction.stabilizer
              (ConjAct P) u) ∣
          403200 := by
      have hGroupDvd :
          Nat.card
              (MulAction.stabilizer
                (ConjAct P) u) ∣
            Nat.card (ConjAct P) :=
        Subgroup.card_subgroup_dvd_card _
      have hGroupDvd' :
          Nat.card
              (MulAction.stabilizer
                (ConjAct P) u) ∣
            1428134400 := by
        rw [hConjActCardExact] at hGroupDvd
        simpa only [Nat.card_eq_fintype_card]
          using hGroupDvd
      have hCentralizerDvd :=
        orderFiveSupport_stabilizer_card_dvd_centralizer
          X P 15 u
      rw [orderFiveSupportFifteen_centralizer_card
        X P hcard u] at hCentralizerDvd
      exact
        dvd_four_hundred_three_thousand_two_hundred
          hGroupDvd' hCentralizerDvd
    have hConjActCard :
        Nat.card (ConjAct P) =
          3542 * 403200 := by
      calc
        Nat.card (ConjAct P) = 1428134400 :=
          hConjActCardExact
        _ = 3542 * 403200 := by norm_num
    have hOrbitDiv :
        3542 ∣
          Nat.card
            (OrderFiveSupportElements X P 15) :=
      divisor_dvd_card_of_stabilizer_card_dvd
        (ConjAct P)
        (OrderFiveSupportElements X P 15)
        3542 403200 hConjActCard hStabilizerDvd
    rw [hGlobalFifteenCard] at hOrbitDiv
    norm_num at hOrbitDiv

end FiveTransitive.Degree24

end CFSG
