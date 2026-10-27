module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem no_order_eight_thousand_one_hundred_five_normalizer_parameters
    (n c r m : ℕ)
    (hnm : n * m = 8100)
    (hnthree : 3 ∣ n)
    (hnmod : n % 5 = 1)
    (hmlower : 300 ≤ m)
    (hTwentyFiveDvdC : 25 ∣ c)
    (hCdvd : c ∣ 750)
    (hrDvd : r ∣ 480)
    (hmEq : m = r * c) :
    False := by
  have hmul : n * 300 ≤ n * m :=
    Nat.mul_le_mul_left n hmlower
  have hnle : n ≤ 27 := by
    omega
  obtain ⟨k, hk⟩ := hnthree
  have hn : n = 6 := by
    interval_cases n <;> norm_num at hnmod <;> omega
  have hm : m = 1350 := by
    rw [hn] at hnm
    omega
  have hcLe : c ≤ 750 :=
    Nat.le_of_dvd (by norm_num) hCdvd
  have hcCases :
      c = 25 ∨ c = 50 ∨ c = 75 ∨ c = 125 ∨
      c = 150 ∨ c = 250 ∨ c = 375 ∨ c = 750 := by
    interval_cases c <;> norm_num at hCdvd
    all_goals norm_num at hTwentyFiveDvdC
    all_goals omega
  rcases hcCases with rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · have hr : r = 54 := by omega
    subst r
    norm_num at hrDvd
  · have hr : r = 27 := by omega
    subst r
    norm_num at hrDvd
  · have hr : r = 18 := by omega
    subst r
    norm_num at hrDvd
  · omega
  · have hr : r = 9 := by omega
    subst r
    norm_num at hrDvd
  · omega
  · omega
  · omega

theorem five_point_stabilizer_card_ne_eight_thousand_one_hundred
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard :
      Nat.card (fixingSubgroup P s) = 8100) :
    False := by
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
    apply
      sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
        K 324 (by norm_num) (by norm_num)
    calc
      Nat.card K = Nat.card H := hKcard
      _ = 8100 := by
        simpa only [H] using hHcard
      _ = 25 * 324 := by norm_num
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
    apply
      sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
        H 324 (by norm_num) (by norm_num)
    calc
      Nat.card H = 8100 := by
        simpa only [H] using hHcard
      _ = 25 * 324 := by norm_num
  letI : IsMulCommutative S :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 5) (by
        rw [hScard]
        norm_num)
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
  let N : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  let n := Nat.card (Sylow 5 H)
  let c := Nat.card C
  let r := C.relIndex N
  let m := Nat.card N
  have hmlower : 300 ≤ m := by
    simpa only [H, S, N, m] using
      sylow_five_card_twenty_five_local_normalizer_ge_three_hundred
        X P hcard h5 hnotAlt s hs S hScard
  have hCdvd : c ∣ 750 := by
    simpa only [H, S, C, c] using
      sylow_five_card_twenty_five_centralizer_card_dvd_seven_hundred_fifty
        X P hcard h5 hnotAlt s hs S hScard
  have hSleC : (S : Subgroup H) ≤ C := by
    intro a ha b hb
    exact
      congrArg Subtype.val
        (mul_comm'
          (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hTwentyFiveDvdC : 25 ∣ c := by
    change 25 ∣ Nat.card C
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSleC
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp
      (H.subtype.comp
        (S : Subgroup H).subtype)
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) :=
    inclusion.range
  let eSR : S ≃* R :=
    MonoidHom.ofInjective hinclusion
  have hRcard : Nat.card R = 25 := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr eSR.symm.toEquiv
      _ = 25 := hScard
  have hAutR : Nat.card (MulAut R) = 480 :=
    mulAut_card_eq_four_hundred_eighty_of_subgroup_card_twenty_five
      X hcard R hRcard
  have hAutCard : Nat.card (MulAut S) = 480 := by
    calc
      Nat.card (MulAut S) =
          Nat.card (MulAut R) :=
        Nat.card_congr (MulAut.congr eSR).toEquiv
      _ = 480 := hAutR
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 480 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      r = Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set H)).relIndex
          (Subgroup.normalizer (S : Set H)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd : r ∣ 480 := by
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
  have hmEq : m = r * c := by
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
    change Nat.card N = r * Nat.card C
    exact
      (Nat.mul_left_cancel
        (Nat.pos_of_ne_zero
          Subgroup.index_ne_zero_of_finite)
        hproduct).symm
  have hNindex : N.index = n := by
    calc
      N.index = Nat.card (Sylow 5 H) :=
        S.card_eq_index_normalizer.symm
      _ = n := rfl
  have hnm : n * m = 8100 := by
    have hproduct := N.index_mul_card
    rw [hNindex] at hproduct
    change n * Nat.card N = 8100
    calc
      n * Nat.card N = Nat.card H := hproduct
      _ = 8100 := by
        simpa only [H] using hHcard
  have hnmod : n % 5 = 1 := by
    have hmod := card_sylow_modEq_one 5 H
    change n % 5 = 1 % 5 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  exact
    no_order_eight_thousand_one_hundred_five_normalizer_parameters
      n c r m hnm (by
        simpa only [n] using hthree)
      hnmod hmlower hTwentyFiveDvdC hCdvd hrDvd hmEq

end FiveTransitive.Degree24

end CFSG
