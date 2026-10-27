module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem no_small_order_twenty_five_sylow_parameters
    (h n m : ℕ)
    (hcases : h = 600 ∨ h = 1200)
    (hnm : n * m = h)
    (hnpos : 0 < n)
    (hnthree : 3 ∣ n)
    (hnmod : n % 5 = 1)
    (hmlower : 300 ≤ m) :
    False := by
  have hhle : h ≤ 1200 := by
    omega
  have hmul : n * 300 ≤ n * m :=
    Nat.mul_le_mul_left n hmlower
  have hnle : n ≤ 4 := by
    omega
  obtain ⟨k, hk⟩ := hnthree
  omega

theorem five_point_stabilizer_card_ne_six_hundred_and_ne_twelve_hundred
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 600 ∧
      Nat.card (fixingSubgroup P s) ≠ 1200 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
    change
      (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
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
  have hnotCases
      (hHcases :
        Nat.card H = 600 ∨ Nat.card H = 1200) :
      False := by
    have hlocalCard
        (e : Fin 5 ↪ X)
        (T : Sylow 5
          (fixingSubgroup P (Set.range e))) :
        Nat.card T = 25 := by
      let K : Subgroup P :=
        fixingSubgroup P (Set.range e)
      have hecard :
          (Set.range e).ncard = 5 := by
        rw [Set.ncard_range_of_injective e.injective,
          Nat.card_eq_fintype_card,
          Fintype.card_fin]
      have hKindexRaw :=
        hP5.index_of_fixingSubgroup_mul hecard
      rw [Nat.card_eq_fintype_card,
        hcard] at hKindexRaw
      norm_num at hKindexRaw
      have hKindex : K.index = 5100480 := by
        change
          (fixingSubgroup P
            (Set.range e)).index = 5100480
        omega
      have hKindexCard := K.index_mul_card
      have hKcard :
          Nat.card K = Nat.card H := by
        rw [hKindex] at hKindexCard
        rw [hHindex] at hHindexCard
        omega
      rcases hHcases with hFirst | hSecond
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            K 24 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card K = Nat.card H := hKcard
            _ = 600 := hFirst
            _ = 25 * 24 := by norm_num)
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            K 48 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card K = Nat.card H := hKcard
            _ = 1200 := hSecond
            _ = 25 * 48 := by norm_num)
    have hthree :
        3 ∣ Nat.card (Sylow 5 H) := by
      have hthreeRange :=
        three_dvd_card_sylow_five_fixing_embedding
          X P hcard h5 hnotAlt e₀ hlocalCard
      rw [he₀Range] at hthreeRange
      exact hthreeRange
    let S : Sylow 5 H :=
      Sylow.nonempty.some
    have hScard : Nat.card S = 25 := by
      rcases hHcases with hFirst | hSecond
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            H 24 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card H = 600 := hFirst
            _ = 25 * 24 := by norm_num)
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            H 48 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card H = 1200 := hSecond
            _ = 25 * 48 := by norm_num)
    let N : Subgroup H :=
      Subgroup.normalizer (S : Set H)
    let n := Nat.card (Sylow 5 H)
    let m := Nat.card N
    have hmlower : 300 ≤ m := by
      simpa only [H, S, N, m] using
        sylow_five_card_twenty_five_local_normalizer_ge_three_hundred
          X P hcard h5 hnotAlt s hs S hScard
    have hNindex : N.index = n := by
      calc
        N.index = Nat.card (Sylow 5 H) :=
          S.card_eq_index_normalizer.symm
        _ = n := rfl
    have hnm :
        n * m = Nat.card H := by
      have hproduct := N.index_mul_card
      rw [hNindex] at hproduct
      exact hproduct
    have hnpos : 0 < n :=
      Nat.card_pos
    have hnmod : n % 5 = 1 := by
      have hmod := card_sylow_modEq_one 5 H
      change n % 5 = 1 % 5 at hmod
      norm_num at hmod
      simpa only [n, Nat.card_eq_fintype_card] using hmod
    exact
      no_small_order_twenty_five_sylow_parameters
        (Nat.card H) n m hHcases hnm hnpos hthree
          hnmod hmlower
  constructor
  · intro h
    exact hnotCases (Or.inl h)
  · intro h
    exact hnotCases (Or.inr h)

end FiveTransitive.Degree24

end CFSG
