module

public import CFSG.Permutation.FiveTransitive.Degree24Order96Three

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem order96_sylow_three_count_cases
    (n : ℕ) (hnDvd : n ∣ 32) (hnMod : n % 3 = 1) :
    n = 1 ∨ n = 4 ∨ n = 16 := by
  have hnLe : n ≤ 32 := Nat.le_of_dvd (by omega) hnDvd
  have hfinite : ∀ q : Fin 33, q.1 ∣ 32 → q.1 % 3 = 1 →
      q.1 = 1 ∨ q.1 = 4 ∨ q.1 = 16 := by decide
  exact hfinite ⟨n, by omega⟩ hnDvd hnMod

private theorem order96_extremal_arithmetic
    (n U t : ℕ) (hn : n = 1 ∨ n = 4 ∨ n = 16)
    (hcount : 5100480 * (n * 2) = U * 720)
    (hbound : 489646080 ≤ U * t) (ht : t ≤ 2160) :
    U = 226688 ∧ t = 2160 := by
  have hU : U = 14168 ∨ U = 56672 ∨ U = 226688 := by
    rcases hn with rfl | rfl | rfl <;> omega
  rcases hU with rfl | rfl | rfl <;> omega

theorem order96_global_orderThree_extremal_data
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96) :
    let U := OrderPrimeSupportElements X P 3 18
    ∃ u : U,
      Nat.card U = 226688 ∧
        Nat.card
          (MulAction.stabilizer (ConjAct P) u) =
            2160 := by
  classical
  dsimp
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
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
  have hPcard : Nat.card P = 489646080 := by
    rw [hHindex,
      show Nat.card H = 96 by
        simpa only [H] using hHcard] at hHindexCard
    omega
  let S : Sylow 3 H := Sylow.nonempty.some
  have hScard : Nat.card S = 3 :=
    sylow_card_eq_prime_of_card_eq_prime_mul
      H 3 32 (by norm_num) (by norm_num)
        (by simpa only [H] using hHcard) S
  have hSindex : S.index = 32 := by
    have hproduct := S.index_mul_card
    rw [hScard] at hproduct
    have hHcard' : Nat.card H = 96 := by
      simpa only [H] using hHcard
    rw [hHcard'] at hproduct
    omega
  let n := Nat.card (Sylow 3 H)
  have hnDvd : n ∣ 32 := by
    have hdiv := S.card_dvd_index
    change n ∣ S.index at hdiv
    simpa only [hSindex] using hdiv
  have hnMod : n % 3 = 1 := by
    have hmod := card_sylow_modEq_one 3 H
    change n % 3 = 1 % 3 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  have hnCases : n = 1 ∨ n = 4 ∨ n = 16 :=
    order96_sylow_three_count_cases n hnDvd hnMod
  have hAllCard :
      Nat.card {u : H // orderOf u = 3} =
        n * 2 := by
    have hcount :=
      card_order_prime_elements_of_sylow_card_prime
        H 3 S hScard
    change
      Nat.card {u : H // orderOf u = 3} =
        n * (3 - 1) at hcount
    norm_num at hcount ⊢
    exact hcount
  have hSupport
      (v : fixingSubgroup P s)
      (hvorder : orderOf v = 3) :
      ((((v : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = 18) :=
    order_three_mem_five_stabilizer_support_eq_eighteen_of_card_eq_ninety_six
      X P hcard h5 hnotAlt s hs hHcard v hvorder
  have hcount :=
    degree24_order_three_support_incidence
      X P hcard hP5 s hs 18 hSupport
  rw [hAllCard] at hcount
  letI : Nontrivial S :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hScard]
      norm_num)
  obtain ⟨w, hwNe⟩ := exists_ne (1 : S)
  have hwOrderS : orderOf w = 3 :=
    Degree15.orderOf_eq_prime_of_card_eq_prime
      hScard hwNe
  let wH : H := w
  have hwOrderH : orderOf wH = 3 := by
    calc
      orderOf wH = orderOf w :=
        Subgroup.orderOf_coe _
      _ = 3 := hwOrderS
  let wP : P := wH
  have hwOrderP : orderOf wP = 3 := by
    calc
      orderOf wP = orderOf wH :=
        Subgroup.orderOf_coe _
      _ = 3 := hwOrderH
  have hwSupport :
      (wP : Equiv.Perm X).support.card = 18 := by
    simpa only [wP, wH, H] using
      hSupport (wH : fixingSubgroup P s) hwOrderH
  let u : OrderPrimeSupportElements X P 3 18 :=
    ⟨wP, ⟨hwOrderP, hwSupport⟩⟩
  let A := MulAction.orbit (ConjAct P) u
  have hOrbitProduct :
      Nat.card A *
          Nat.card
            (MulAction.stabilizer (ConjAct P) u) =
        Nat.card P := by
    have hproduct :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (ConjAct P) u
    rw [ConjAct.card,
      ← Nat.card_eq_fintype_card] at hproduct
    simpa only [A, Nat.card_eq_fintype_card] using hproduct
  let orbitInclusion :
      A → OrderPrimeSupportElements X P 3 18 :=
    fun a => a.1
  have hOrbitInclusionInjective :
      Function.Injective orbitInclusion :=
    fun _ _ h => Subtype.ext h
  have hOrbitLe :
      Nat.card A ≤
        Nat.card
          (OrderPrimeSupportElements X P 3 18) :=
    Nat.card_le_card_of_injective
      orbitInclusion hOrbitInclusionInjective
  have hStabilizerDvd :
      Nat.card
          (MulAction.stabilizer (ConjAct P) u) ∣
        2160 :=
    orderThreeSupportEighteen_stabilizer_card_dvd_two_thousand_one_hundred_sixty
      X P hcard h5 hnotAlt hPcard u
  have hStabilizerLe :
      Nat.card
          (MulAction.stabilizer (ConjAct P) u) ≤
        2160 :=
    Nat.le_of_dvd (by norm_num) hStabilizerDvd
  have hPLe :
      Nat.card P ≤
        Nat.card (OrderPrimeSupportElements X P 3 18) *
          Nat.card (MulAction.stabilizer (ConjAct P) u) := by
    rw [← hOrbitProduct]
    exact Nat.mul_le_mul_right _ hOrbitLe
  rw [hPcard] at hPLe
  have hcount' : 5100480 * (n * 2) =
      Nat.card (OrderPrimeSupportElements X P 3 18) * 720 := by
    simpa only [show (24 - 18).descFactorial 5 = 720 by decide] using hcount
  obtain ⟨hUcard, hStabilizerCard⟩ :=
    order96_extremal_arithmetic n
      (Nat.card (OrderPrimeSupportElements X P 3 18))
      (Nat.card (MulAction.stabilizer (ConjAct P) u))
      hnCases hcount' hPLe hStabilizerLe
  exact ⟨u, hUcard, hStabilizerCard⟩

theorem order96_orderThree_support_conjugation_pretransitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96) :
    MulAction.IsPretransitive
      (ConjAct P)
      (OrderPrimeSupportElements X P 3 18) := by
  classical
  obtain ⟨u, hUcard, hStabilizerCard⟩ :=
    order96_global_orderThree_extremal_data
      X P hcard h5 hnotAlt s hs hHcard
  have hP5 :
      MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  let H : Subgroup P := fixingSubgroup P s
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 489646080 := by
    rw [hHindex,
      show Nat.card H = 96 by
        simpa only [H] using hHcard] at hHindexCard
    omega
  let A := MulAction.orbit (ConjAct P) u
  have hOrbitProduct :
      Nat.card A *
          Nat.card
            (MulAction.stabilizer (ConjAct P) u) =
        Nat.card P := by
    have hproduct :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (ConjAct P) u
    rw [ConjAct.card,
      ← Nat.card_eq_fintype_card] at hproduct
    simpa only [A, Nat.card_eq_fintype_card] using hproduct
  have hAcard : Nat.card A = 226688 := by
    rw [hStabilizerCard, hPcard] at hOrbitProduct
    omega
  have hOrbitEq :
      MulAction.orbit (ConjAct P) u = Set.univ := by
    apply Set.eq_top_of_card_le_of_finite
    change
      Nat.card
          (OrderPrimeSupportElements X P 3 18) ≤
        Nat.card A
    rw [hUcard, hAcard]
  rw [MulAction.isPretransitive_iff_orbit_eq_univ u]
  exact hOrbitEq

end FiveTransitive.Degree24

end CFSG
