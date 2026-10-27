module

public import CFSG.Permutation.FiveTransitive.Degree24SevenTransferCases

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem small_seven_normalizer_arithmetic
    {h n c r m : ℕ}
    (hCases :
      h = 3360 ∨ h = 4082400 ∨ h = 48384 ∨
      h = 26127360 ∨ h = 1161216)
    (hnm : n * m = h)
    (hnMod : n % 7 = 1)
    (hThree : 3 ∣ n)
    (hSeven : 7 ∣ c)
    (hcDvd : c ∣ 98)
    (hrDvd : r ∣ 6)
    (hm : m = r * c) :
    m ≤ 28 := by
  rcases
      card_eq_seven_fourteen_forty_nine_or_ninety_eight
        hSeven hcDvd with
    rfl | rfl | rfl | rfl
  all_goals
    rcases divisor_six_cases hrDvd with
      rfl | rfl | rfl | rfl
  all_goals
    rcases hCases with
      rfl | rfl | rfl | rfl | rfl
  all_goals
    subst m
  all_goals omega

theorem small_seven_local_normalizer_card_le
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 3360 ∨
      Nat.card (fixingSubgroup P s) = 4082400 ∨
      Nat.card (fixingSubgroup P s) = 48384 ∨
      Nat.card (fixingSubgroup P s) = 26127360 ∨
      Nat.card (fixingSubgroup P s) = 1161216)
    (S : Sylow 7 (fixingSubgroup P s)) :
    Nat.card
        (Subgroup.normalizer
          (S : Set (fixingSubgroup P s))) ≤
      28 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  let n := Nat.card (Sylow 7 H)
  have hScard : Nat.card S = 7 := by
    rcases hCases with hH | hH | hH | hH | hH
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 480 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 583200 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 6912 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 3732480 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 165888 (by norm_num) (by norm_num)
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
        hThreeGlobal with hbad | hgood
    · norm_num at hbad
    · exact hgood
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
  apply
    small_seven_normalizer_arithmetic
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

end FiveTransitive.Degree24

end CFSG
