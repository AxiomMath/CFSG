module

public import CFSG.Permutation.FiveTransitive.Degree24SevenCentralizerBound
public import CFSG.Permutation.FiveTransitive.Degree24Order1050

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private abbrev DivisorNinetyEight :=
  ↥(Nat.divisors 98)

private def divisorNinetyEightPredicate
    (c : DivisorNinetyEight) : Prop :=
  7 ∣ c.1 →
    c.1 = 7 ∨ c.1 = 14 ∨
      c.1 = 49 ∨ c.1 = 98

private theorem divisorNinetyEight_cases :
    ∀ c : DivisorNinetyEight,
      divisorNinetyEightPredicate c := by
  letI (c : DivisorNinetyEight) :
      Decidable (divisorNinetyEightPredicate c) := by
    dsimp only [divisorNinetyEightPredicate]
    infer_instance
  letI : Decidable
      (∀ c : DivisorNinetyEight,
        divisorNinetyEightPredicate c) :=
    Fintype.decidableForallFintype
  decide

theorem card_eq_seven_fourteen_forty_nine_or_ninety_eight
    {c : ℕ} (hSeven : 7 ∣ c) (hDvd : c ∣ 98) :
    c = 7 ∨ c = 14 ∨ c = 49 ∨ c = 98 := by
  have hcMem : c ∈ Nat.divisors 98 :=
    Nat.mem_divisors.mpr ⟨hDvd, by norm_num⟩
  exact divisorNinetyEight_cases ⟨c, hcMem⟩ hSeven

private abbrev DivisorSix :=
  ↥(Nat.divisors 6)

private def divisorSixPredicate (r : DivisorSix) : Prop :=
  r.1 = 1 ∨ r.1 = 2 ∨ r.1 = 3 ∨ r.1 = 6

private theorem divisorSix_cases :
    ∀ r : DivisorSix, divisorSixPredicate r := by
  letI (r : DivisorSix) :
      Decidable (divisorSixPredicate r) := by
    dsimp only [divisorSixPredicate]
    infer_instance
  letI : Decidable
      (∀ r : DivisorSix, divisorSixPredicate r) :=
    Fintype.decidableForallFintype
  decide

theorem divisor_six_cases
    {r : ℕ} (hrDvd : r ∣ 6) :
    r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 6 := by
  have hrMem : r ∈ Nat.divisors 6 :=
    Nat.mem_divisors.mpr ⟨hrDvd, by norm_num⟩
  exact divisorSix_cases ⟨r, hrMem⟩

private theorem selected_seven_normalizer_arithmetic
    {h n c r m : ℕ}
    (hCases :
      h = 2016 ∨ h = 1088640)
    (hnm : n * m = h)
    (hnMod : n % 7 = 1)
    (hThree : 3 ∣ n)
    (hSeven : 7 ∣ c)
    (hcDvd : c ∣ 98)
    (hrDvd : r ∣ 6)
    (hm : m = r * c) :
    r = 1 := by
  rcases
      card_eq_seven_fourteen_forty_nine_or_ninety_eight
        hSeven hcDvd with
    rfl | rfl | rfl | rfl
  all_goals
    rcases divisor_six_cases hrDvd with
      rfl | rfl | rfl | rfl
  all_goals
    rcases hCases with rfl | rfl
  all_goals
    subst m
  all_goals omega

theorem global_orderSevenSupportFourteen_card_eq_sylow_count_mul
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s))
    (hScard : Nat.card S = 7) :
    Nat.card
        (OrderPrimeSupportElements X P 7 14) =
      1012 *
        Nat.card
          (Sylow 7 (fixingSubgroup P s)) := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let n := Nat.card (Sylow 7 H)
  have hAllCard :
      Nat.card {u : H // orderOf u = 7} =
        n * 6 := by
    have hcount :=
      card_order_prime_elements_of_sylow_card_prime
        H 7 S hScard
    change
      Nat.card {u : H // orderOf u = 7} =
        n * (7 - 1) at hcount
    norm_num at hcount
    simpa only [Nat.card_eq_fintype_card] using hcount
  have hSupport
      (u : fixingSubgroup P s)
      (hu : orderOf u = 7) :
      ((((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = 14) :=
    order_seven_mem_five_stabilizer_support_eq_fourteen
      X P hcard h5 hnotAlt s hs u hu
  let localEquiv :
      {u : H // orderOf u = 7} ≃
        LocalOrderPrimeSupportElements X P s 7 14 := {
    toFun := fun u =>
      ⟨u.1, ⟨u.2, hSupport u.1 u.2⟩⟩
    invFun := fun u => ⟨u.1, u.2.1⟩
    left_inv := by
      intro u
      apply Subtype.ext
      rfl
    right_inv := by
      intro u
      apply Subtype.ext
      rfl }
  have hLocalCard :
      Nat.card
          (LocalOrderPrimeSupportElements
            X P s 7 14) =
        n * 6 := by
    rw [← Nat.card_congr localEquiv, hAllCard]
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
  have hLocal :
      Nat.card
          (LocalOrderPrimeSupportElements
            X P s 7 14) =
        Nat.card
          (OrderPrimeSupportFixesEmbedding
            X P 7 14 e₀) :=
    Nat.card_congr
      (localOrderPrimeSupportEquiv
        X P s 7 14 e₀ he₀Range)
  have hP5 :
      MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hfixed
      (u : OrderPrimeSupportElements X P 7 14) :
      Nat.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
        30240 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
          (Fintype.card
            (MulAction.fixedBy X u.1)).descFactorial
              (Fintype.card (Fin 5)) :=
        Degree15.card_fixedBy_embedding
          (G := P) (X := X) (I := Fin 5) u.1
      _ = 30240 := by
        rw [Degree15.card_fixedBy_subgroup_perm,
          hcard, u.2.2, Fintype.card_fin]
        norm_num [Nat.descFactorial]
  have hEcard : Nat.card (Fin 5 ↪ X) = 5100480 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq,
      Fintype.card_fin, hcard]
    norm_num [Nat.descFactorial]
  have hcount :=
    orderPrimeSupport_incidence_count
      X P hP5 7 14 30240 hfixed e₀
  rw [hEcard, ← hLocal, hLocalCard] at hcount
  change
    Nat.card
        (OrderPrimeSupportElements X P 7 14) =
      1012 * n
  exact
    degree24_global_support_fourteen_card_of_local_sylow_count
      hcount

theorem selected_sylowSeven_normalizer_le_centralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 2016 ∨
      Nat.card (fixingSubgroup P s) = 1088640)
    (S : Sylow 7 (fixingSubgroup P s)) :
    Subgroup.normalizer
        (S : Set (fixingSubgroup P s)) ≤
      Subgroup.centralizer
        (S : Set (fixingSubgroup P s)) := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  let n := Nat.card (Sylow 7 H)
  have hScard : Nat.card S = 7 := by
    rcases hCases with hH | hH
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 288 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 155520 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  have hGlobalCard :
      Nat.card
          (OrderPrimeSupportElements X P 7 14) =
        1012 * n := by
    simpa only [H, n] using
      global_orderSevenSupportFourteen_card_eq_sylow_count_mul
        X P hcard h5 hnotAlt s hs S hScard
  obtain ⟨u, huOrderRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard
      (α := S)
  have huOrder : orderOf u = 7 :=
    huOrderRaw.trans hScard
  have hSupport :
      (((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 14) :=
    order_seven_mem_five_stabilizer_support_eq_fourteen
      X P hcard h5 hnotAlt s hs (u : H) (by
        calc
          orderOf (u : H) = orderOf u :=
            Subgroup.orderOf_coe _
          _ = 7 := huOrder)
  have hGlobalNonempty :
      Nonempty
        (OrderPrimeSupportElements X P 7 14) := by
    exact
      ⟨⟨(((u : S) : H) : P),
        ⟨by
          calc
            orderOf ((((u : S) : H) : P)) =
                orderOf ((u : S) : H) :=
              Subgroup.orderOf_coe _
            _ = orderOf u :=
              Subgroup.orderOf_coe _
            _ = 7 := huOrder,
        hSupport⟩⟩⟩
  have hThreeGlobal :
      3 ∣
        Nat.card
          (OrderPrimeSupportElements X P 7 14) :=
    three_dvd_card_orderSevenSupportElements
      X P 14 hGlobalNonempty
  have hThreeN : 3 ∣ n := by
    rw [hGlobalCard] at hThreeGlobal
    rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp
        hThreeGlobal with h | h
    · norm_num at h
    · exact h
  have hnMod : n % 7 = 1 := by
    have hmod := card_sylow_modEq_one 7 H
    change n % 7 = 1 % 7 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
  let N : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  let r := C.relIndex N
  have hCdvd : Nat.card C ∣ 98 := by
    simpa only [H, C] using
      sylowSeven_centralizer_card_dvd_ninety_eight
        X P hcard h5 hnotAlt s hs S hScard
  have hSleC : (S : Subgroup H) ≤ C := by
    intro a ha b hb
    exact
      congrArg Subtype.val
        (mul_comm'
          (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hSevenDvdC : 7 ∣ Nat.card C := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSleC
  have hAutCard : Nat.card (MulAut S) = 6 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 6 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      r =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set H)).relIndex
          (Subgroup.normalizer (S : Set H)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd : r ∣ 6 := by
    rw [hrEq]
    exact hrangeDvd
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrel :
      r * N.index = C.index := by
    exact
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer
          (S : Set H))
  have hNcardEq :
      Nat.card N = r * Nat.card C := by
    have hproduct :
        N.index * (r * Nat.card C) =
          N.index * Nat.card N := by
      calc
        N.index * (r * Nat.card C) =
            C.index * Nat.card C := by
          rw [← hrel]
          ac_rfl
        _ = Nat.card H := C.index_mul_card
        _ = N.index * Nat.card N :=
          N.index_mul_card.symm
    exact
      (Nat.mul_left_cancel
        (Nat.pos_of_ne_zero
          Subgroup.index_ne_zero_of_finite)
        hproduct).symm
  have hNindex : N.index = n := by
    calc
      N.index = Nat.card (Sylow 7 H) :=
        S.card_eq_index_normalizer.symm
      _ = n := rfl
  have hnN : n * Nat.card N = h := by
    have hproduct := N.index_mul_card
    rw [hNindex] at hproduct
    exact hproduct
  have hrOne : r = 1 := by
    apply
      selected_seven_normalizer_arithmetic
        (h := h) (n := n) (c := Nat.card C)
        (r := r) (m := Nat.card N)
    · simpa only [H, h] using hCases
    · exact hnN
    · exact hnMod
    · exact hThreeN
    · exact hSevenDvdC
    · exact hCdvd
    · exact hrDvd
    · exact hNcardEq
  exact Subgroup.relIndex_eq_one.mp
    (show C.relIndex N = 1 by
      simpa only [r] using hrOne)

end FiveTransitive.Degree24

end CFSG
