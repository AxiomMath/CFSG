module

public import CFSG.Permutation.FiveTransitive.Degree24SevenTransferCases

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem rSix_seven_normalizer_arithmetic
    {h n c r m : ℕ}
    (hCases :
      h = 13608 ∨ h = 13063680)
    (hnm : n * m = h)
    (hnMod : n % 7 = 1)
    (hThree : 3 ∣ n)
    (hSeven : 7 ∣ c)
    (hcDvd : c ∣ 98)
    (hrDvd : r ∣ 6)
    (hm : m = r * c) :
    c = 14 ∧ r = 6 ∧ m = 84 := by
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

theorem rSix_sylowSeven_local_data
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 13608 ∨
      Nat.card (fixingSubgroup P s) = 13063680)
    (S : Sylow 7 (fixingSubgroup P s)) :
    Nat.card
        (Subgroup.centralizer
          (S : Set (fixingSubgroup P s))) = 14 ∧
      (Subgroup.centralizer
          (S : Set (fixingSubgroup P s))).relIndex
        (Subgroup.normalizer
          (S : Set (fixingSubgroup P s))) = 6 ∧
      Nat.card
        (Subgroup.normalizer
          (S : Set (fixingSubgroup P s))) = 84 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  let n := Nat.card (Sylow 7 H)
  have hScard : Nat.card S = 7 := by
    rcases hCases with hH | hH
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 1944 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 1866240 (by norm_num) (by norm_num)
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
  have hdata :
      Nat.card C = 14 ∧ r = 6 ∧
        Nat.card N = 84 := by
    apply
      rSix_seven_normalizer_arithmetic
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
  simpa only [H, C, N, r] using hdata

theorem rSix_orderSeven_elements_are_conjugate
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 13608 ∨
      Nat.card (fixingSubgroup P s) = 13063680)
    (u v : fixingSubgroup P s)
    (hu : orderOf u = 7) (hv : orderOf v = 7) :
    ∃ q : fixingSubgroup P s,
      q * u * q⁻¹ = v := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let R : Subgroup H := Subgroup.zpowers u
  have hRcard : Nat.card R = 7 := by
    rw [Nat.card_zpowers, hu]
  have hRisP : IsPGroup 7 R := by
    apply IsPGroup.of_card (n := 1)
    rw [hRcard]
    norm_num
  obtain ⟨S, hRleS⟩ := hRisP.exists_le_sylow
  have hScard : Nat.card S = 7 := by
    rcases hCases with hH | hH
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 1944 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 1866240 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
  have hRS : R = (S : Subgroup H) := by
    apply Subgroup.eq_of_le_of_card_ge hRleS
    rw [hRcard, hScard]
  have hlocal :=
    rSix_sylowSeven_local_data
      X P hcard h5 hnotAlt s hs hCases S
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
  let N : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  have hCcard : Nat.card C = 14 := by
    simpa only [H, C] using hlocal.1
  have hNcard : Nat.card N = 84 := by
    simpa only [H, N] using hlocal.2.2
  have hcentEq :
      Subgroup.centralizer ({u} : Set H) = C := by
    apply le_antisymm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff] at hq ⊢
      intro x hx
      have hxR : x ∈ R := by
        rw [hRS]
        exact hx
      obtain ⟨z, hz⟩ :=
        Subgroup.mem_zpowers_iff.mp hxR
      have huq : Commute u q := by
        exact hq u (by simp)
      rw [← hz]
      exact (huq.zpow_left z).eq
    · change
        Subgroup.centralizer (S : Set H) ≤
          Subgroup.centralizer ({u} : Set H)
      apply Subgroup.centralizer_le
      rw [Set.singleton_subset_iff]
      have huR : u ∈ R :=
        Subgroup.mem_zpowers u
      rw [hRS] at huR
      exact huR
  let O := MulAction.orbit (ConjAct H) u
  let A := {w : H // orderOf w = 7}
  letI : Fintype O := Fintype.ofFinite _
  letI : Fintype A := Fintype.ofFinite _
  letI :
      Fintype
        (MulAction.stabilizer (ConjAct H) u) :=
    Fintype.ofFinite _
  have hStabilizerCard :
      Fintype.card
          (MulAction.stabilizer (ConjAct H) u) =
        14 := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.nat_card_centralizer_nat_card_stabilizer,
      hcentEq, hCcard]
  have hOrbitMul :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct H) u
  rw [hStabilizerCard, ConjAct.card,
    ← Nat.card_eq_fintype_card] at hOrbitMul
  rw [← Nat.card_eq_fintype_card] at hOrbitMul
  have hNindex :
      N.index = Nat.card (Sylow 7 H) := by
    simpa only [N] using
      S.card_eq_index_normalizer.symm
  have hHcard :
      Nat.card H =
        Nat.card (Sylow 7 H) * 84 := by
    have hproduct := N.index_mul_card
    rw [hNindex, hNcard] at hproduct
    exact hproduct.symm
  have hOcard :
      Nat.card O =
        Nat.card (Sylow 7 H) * 6 := by
    rw [hHcard] at hOrbitMul
    nlinarith
  have hAcard :
      Nat.card A =
        Nat.card (Sylow 7 H) * 6 := by
    have hcount :=
      card_order_prime_elements_of_sylow_card_prime
        H 7 S hScard
    change
      Nat.card A =
        Nat.card (Sylow 7 H) * (7 - 1) at hcount
    norm_num at hcount
    simpa only [A, Nat.card_eq_fintype_card] using hcount
  let f : O → A :=
    fun a =>
      ⟨a.1, by
        obtain ⟨q, hq⟩ :=
          isConj_iff.mp
            (ConjAct.mem_orbit_conjAct.mp a.prop)
        calc
          orderOf a.1 =
              orderOf ((MulAut.conj q) a.1) :=
            ((MulAut.conj q).orderOf_eq a.1).symm
          _ = orderOf u := congrArg orderOf hq
          _ = 7 := hu⟩
  have hfInjective : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    simpa only [f] using
      congrArg Subtype.val hab
  have hfCard : Nat.card O = Nat.card A := by
    rw [hOcard, hAcard]
  have hfSurjective : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfInjective, hfCard⟩).2
  obtain ⟨a, ha⟩ :=
    hfSurjective (⟨v, hv⟩ : A)
  have hav : a.1 = v :=
    congrArg Subtype.val ha
  obtain ⟨q, hq⟩ :=
    isConj_iff.mp
      (ConjAct.mem_orbit_conjAct.mp a.prop)
  refine ⟨q⁻¹, ?_⟩
  rw [hav] at hq
  calc
    q⁻¹ * u * (q⁻¹)⁻¹ =
        q⁻¹ * (q * v * q⁻¹) * (q⁻¹)⁻¹ := by
      rw [hq]
    _ = v := by group

end FiveTransitive.Degree24

end CFSG
