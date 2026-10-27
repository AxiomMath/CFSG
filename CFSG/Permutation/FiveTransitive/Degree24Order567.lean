module

public import CFSG.Permutation.FiveTransitive.Degree24PrimeSupportIncidence
public import CFSG.Permutation.FiveTransitive.Degree24OrbitDivisibility

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem degree24_global_support_fourteen_card
    {a : ℕ}
    (h : 5100480 * 6 = a * 30240) :
    a = 1012 := by
  omega

private theorem dvd_one_million_two_hundred_seventy_thousand_eighty
    {k : ℕ}
    (hGroup : k ∣ 2891972160)
    (hCentralizer : k ∣ 355622400) :
    k ∣ 1270080 := by
  have hGcd := Nat.dvd_gcd hGroup hCentralizer
  norm_num at hGcd ⊢
  exact hGcd

theorem order_seven_mem_five_stabilizer_support_eq_fourteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (u : fixingSubgroup P s)
    (huorder : orderOf u = 7) :
    ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 14) := by
  classical
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf (u : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsFixed :
      s ⊆ MulAction.fixedBy X (u : P) := by
    intro x hx
    exact
      (mem_fixingSubgroup_iff P).mp u.prop x hx
  have hfixedAtLeast :
      5 ≤ Fintype.card
        (MulAction.fixedBy X (u : P)) := by
    calc
      5 = s.ncard := hs.symm
      _ ≤ (MulAction.fixedBy X (u : P)).ncard :=
        Set.ncard_le_ncard hsFixed
      _ = Fintype.card
          (MulAction.fixedBy X (u : P)) := by
        rw [← Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card]
  have hsupportLe : g.support.card ≤ 19 := by
    have huSupportLe :
        (((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card ≤ 19 := by
      rw [Degree15.card_fixedBy_subgroup_perm,
        hcard] at hfixedAtLeast
      omega
    exact huSupportLe
  have hkCases :
      k + 1 = 1 ∨ k + 1 = 2 := by
    have hkLe : k + 1 ≤ 2 := by
      by_contra hle
      have hthree : 3 ≤ k + 1 := by omega
      have htwentyOne :
          21 ≤ g.support.card := by
        calc
          21 = 3 * 7 := by norm_num
          _ ≤ (k + 1) * 7 :=
            Nat.mul_le_mul_right 7 hthree
          _ = g.support.card := hsum
      omega
    omega
  rcases hkCases with hkOne | hkTwo
  · have hsupport : g.support.card = 7 := by
      omega
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5
          ((u : P).prop)
          (by
            intro hu
            have huP : (u : P) = 1 :=
              Subtype.ext hu
            have hgOne : g = 1 := by
              change
                ((u : P) : Equiv.Perm X) = 1
              exact congrArg Subtype.val huP
            rw [hgOne, orderOf_one] at hgorder
            norm_num at hgorder)
          (by
            change g.support.card ≤ 7
            omega)))
  · simpa only [g] using
      (show g.support.card = 14 by omega)

private theorem orderSevenSupportFourteen_centralizer_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (u : OrderPrimeSupportElements X P 7 14) :
    Nat.card
        (Subgroup.centralizer
          ({(u.1 : Equiv.Perm X)} :
            Set (Equiv.Perm X))) =
      355622400 := by
  classical
  let g : Equiv.Perm X := u.1
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = 7 := u.2.1
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, u.2.2] at hsum
  have hkTwo : k + 1 = 2 := by omega
  have hcycleType : g.cycleType = {7, 7} := by
    rw [hk, hgorder, hkTwo]
    norm_num
  change
    Nat.card
        (Subgroup.centralizer
          ({g} : Set (Equiv.Perm X))) =
      355622400
  rw [Equiv.Perm.nat_card_centralizer,
    hcycleType, hcard]
  norm_num

theorem five_point_stabilizer_card_ne_five_hundred_sixty_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 567 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
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
      Nat.card P = 2891972160 := by
    rw [hPcard, hHcard]
  let S : Sylow 7 H := Sylow.nonempty.some
  have hScard : Nat.card S = 7 :=
    sylow_card_eq_prime_of_card_eq_prime_mul
      H 7 81 (by norm_num) (by norm_num)
        (by simpa using hHcard) S
  have hSindex : S.index = 81 := by
    have hproduct := S.index_mul_card
    rw [hScard, hHcard] at hproduct
    omega
  let n := Nat.card (Sylow 7 H)
  have hnDvd : n ∣ 81 := by
    have hdiv := S.card_dvd_index
    change n ∣ S.index at hdiv
    simpa [hSindex] using hdiv
  have hnMod : n % 7 = 1 := by
    have hmod := card_sylow_modEq_one 7 H
    change n % 7 = 1 % 7 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  have hnOne : n = 1 := by
    have hnPow : n ∣ 3 ^ 4 := by
      norm_num
      exact hnDvd
    obtain ⟨j, hj, hn⟩ :=
      (Nat.dvd_prime_pow
        (by norm_num : Nat.Prime 3)).mp hnPow
    rw [hn] at hnMod ⊢
    interval_cases j <;> norm_num at hnMod
    norm_num
  have hAllCard :
      Nat.card {u : H // orderOf u = 7} = 6 := by
    have hcount :=
      card_order_prime_elements_of_sylow_card_prime
        H 7 S hScard
    change
      Nat.card {u : H // orderOf u = 7} =
        n * (7 - 1) at hcount
    rw [hnOne] at hcount
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
        6 := by
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
  have hGlobalCard :
      Nat.card
          (OrderPrimeSupportElements X P 7 14) =
        1012 :=
    degree24_global_support_fourteen_card hcount
  have hConjActCardExact :
      Nat.card (ConjAct P) =
        2891972160 := by
    rw [Nat.card_eq_fintype_card,
      ConjAct.card,
      ← Nat.card_eq_fintype_card,
      hPcardExact]
  have hStabilizerDvd
      (u : OrderPrimeSupportElements X P 7 14) :
      Nat.card
          (MulAction.stabilizer
            (ConjAct P) u) ∣
        1270080 := by
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
          2891972160 := by
      rw [hConjActCardExact] at hGroupDvd
      simpa only [Nat.card_eq_fintype_card]
        using hGroupDvd
    have hCentralizerDvd :=
      orderPrimeSupport_stabilizer_card_dvd_centralizer
        X P 7 14 u
    rw [orderSevenSupportFourteen_centralizer_card
      X P hcard u] at hCentralizerDvd
    exact
      dvd_one_million_two_hundred_seventy_thousand_eighty
        hGroupDvd' hCentralizerDvd
  have hConjActCard :
      Nat.card (ConjAct P) =
        2277 * 1270080 := by
    calc
      Nat.card (ConjAct P) = 2891972160 :=
        hConjActCardExact
      _ = 2277 * 1270080 := by norm_num
  have hOrbitDiv :
      2277 ∣
        Nat.card
          (OrderPrimeSupportElements X P 7 14) :=
    divisor_dvd_card_of_stabilizer_card_dvd
      (ConjAct P)
      (OrderPrimeSupportElements X P 7 14)
      2277 1270080 hConjActCard hStabilizerDvd
  rw [hGlobalCard] at hOrbitDiv
  norm_num at hOrbitDiv

end FiveTransitive.Degree24

end CFSG
